# This script is for doing secure voting.
# It uses the ElGamal homomorphic encryption scheme for encrypting
# and tallying the votes. It uses the Pedersen protocol for key
# generation. Instead of having a smaller number of authorities that
# voters need to trust, voters trust only themselves. Votes can only be
# tallied if every voter participates.
# Uses the zero knowledge proofs from this paper: 
# http://www.win.tue.nl/~berry/papers/euro97.pdf


from functools import reduce
from operator import and_
from fractions import gcd as fractions_gcd
import random

def prod(iterable):
    """Works the same as sum() but with multiplication."""

    return reduce(lambda x,y: x*y, iterable)

def randint(r):
    return random.SystemRandom().randint(0, r-1)

def mod_div(n, d, m):
    """Returns (n/d) mod m. Works because the modular multiplicative
    inverse of d is equal to d^(m-2) mod m as long as m is prime."""

    inverse = pow(d, m-2, m)
    return (n*inverse) % m

def gcd(a, b): # TODO: might need to implement ourselves
    return fractions_gcd(a, b)

def phi(n):
    """Euler's totient function."""

    return sum(1 for k in range(1, n+1) if gcd(k, n) == 1)

def primitive_roots(p, g, l):
    """Finds another primitive root of p using g (assumed to be a generator).
    p is also assumed to equal 2q+1 where q is another prime. l is the number
    of primitive roots desired. This will just be used on the server."""

    q = (p-1)//2
    roots = tuple(pow(g, (k*2)+1, p) for k in range(1, l+1) if 2*k+1 != q)
    if len(roots) < l: # why am I handling this edge case, it's crazy
        # this is because it's possible 2l+1 > q, and since q|p-1, we can't use it
        # (see it is excluded in the tuple generator above). Thus we might have to
        # add one more. But if p is of reasonable size, this would mean l is crazy
        # big and the program will run out of memory... whatever
        roots = roots + (pow(g, ((l+1)*2)+1, p),)

    return roots

def next_primitive_root(p, g, e=1):
    assert e % 2 == 1, "e should be odd."
    e += 2
    root = pow(g, e, p)
    assert is_primitive_root(p, root)
    return (root, e)

def get_valid_prim_root(p, g):
    e = 1
    q = (p-1)//2
    while (pow(g, q, p) != 1):
        print(e)
        (g, e) = next_primitive_root(p, g, e)

    return g


def is_primitive_root(p, g):
    """Tests if g is a primitive root of n. Assumes p is a prime and
    p = 2q+1 for some prime q."""
    q = (p-1)//2

    #test1 = pow(g, q, p) 
    #test2 = pow(g, 2, p)
    #print(test1, test2)
    if (pow(g, q, p) != 1) and (pow(g, 2, p) != 1):
        return True
    else:
        return False


def elgamal_encrypt(message, public_key, g, p, q):
    """This is how ElGamal encryption works. However, we don't
    actually use this function. Just an example."""

    m = pow(g, message, p)
    r = randint(q)
    x = pow(g, r, p)
    y = (pow(public_key, r, p) * m) % p
    return (x, y)


def beacon(p_id, vals, q):
    #r = randint(q)
    r = 23423452356 # TODO: make this a real thing
    return r



## The following would be on the server, represents the public bulletin board ##
public_key_shares = {}
def publish_public_key_share(p_id, share):
    public_key_shares[p_id] = share

def get_public_key_shares():
    return public_key_shares


pedersen_commits = {}
def publish_pedersen_commit(p_id, commit):
    assert len(commit) == 5, "Pedersen commit should be 5 numbers."
    pedersen_commits[p_id] = (commit)

def get_pedersen_commit(p_id):
    if p_id in pedersen_commits:
        return pedersen_commits[p_id]
    else:
        return None
## end server stuff ##




class Pedersen:
    def __init__(self, p, g, n, party_id, num_votes): # TODO: deal with q and g and p
        assert 0 <= party_id < n, "ID must be less than n."
        self.p = p
        self.q = (p-1)//2
        self.g = g
        self.n = n
        self.party_id = party_id
        self.num_votes = num_votes

        #self.public_key_shares = {}
        self.proofs = {}
        self.pedersen_commits_verified = {p_id: False for p_id in range(n) if p_id != self.party_id}
        self.global_decrypt_shares = {}

        #self.poly = gen_poly(n, q)
        self.secret = randint(q) #TODO: make sure this is good#self.poly[0] # poly(0) is our secret part of the public key
        self.public_key_share = pow(g, self.secret, p) # TODO: make sure this is p
        publish_public_key_share(party_id, self.public_key_share)

        #self.shares = {} # format is {p_id: (share, commit)}
        #for p_id in range(n):
        #    if p_id != self.party_id: # we don't publish our own share
        #        share = eval_poly(self.poly, p_id+1, q)
        #        commit = pow(g, share, p) # g^share mod p is the verifiable commit
        #        self.shares[p_id] = (share, commit)

    #def receive_public_key_share(self, p_id, share):
    #    self.public_key_shares[p_id] = share

    """def sum_shares(self):
        assert len(self.global_shares) == self.n-1, "Have not received all shares."
        assert len(self.public_key_shares) == self.n-1, "Have not received all shares."
        self.global_share = sum(x[0] for x in self.global_shares.values())
        
        # We now have every commit
        m = prod(self.public_key_shares.values())
        self.public_key = (m * self.public_key_share) % self.p
        """

    def make_public_key(self):
        public_key_shares = get_public_key_shares() # from the bulletin board
        if len(public_key_shares) != self.n:
            print("Not everyone has publish their share of the public key yet.")
            return

        assert public_key_shares[self.party_id] == self.public_key_share, "Someone changed our share on the bulletin board!"
        
        self.public_key_shares = public_key_shares
        self.public_key = prod(public_key_shares.values()) % p
    
    def log_ZKP_prove(self, ciphertexts):
        self.ciphertexts = ciphertexts
        #x = ciphertext[0]
        #y = ciphertext[1]

        g = self.g 
        p = self.p
        q = self.q

        h = tuple(c[0] for c in ciphertexts)
        self.h = h

        # w is our share of the decrypted ciphertext
        w = (randint(q),) * self.num_votes
        a = tuple(pow(g, w_i, p) for w_i in w)
        b = tuple(pow(h_i, w_i, p) for w_i, h_i in zip(w, h))

        decrypt_shares = tuple(pow(h_i, self.secret, p) for h_i in h)
        self.decrypt_shares = decrypt_shares # we need w for decription later and for step 2
        x = self.public_key_share
        y = decrypt_shares # the name in the protocol in figure 2
        alpha = self.secret # TODO: double check


        # We now need to prove that log_g(self.public_key_share) == log_x(w)
        # or, in other words, we haven't changed our secret when calculating w
        # This is done using the zero knowledge proof from Pedersen

        commit0 = (y, w, a, b)
        c = tuple(beacon(self.party_id, (x,) + com, q) for com in zip(y, w, a, b))

        r = tuple((w_i + alpha*c_i) % q for w_i, c_i in zip(w, c)) # TODO: pretty sure about this q, maybe double check it

        commit = commit0 + (r,)

        publish_pedersen_commit(self.party_id, commit) # now anyone should be able to verify that w is #legit

    def log_ZKP_verify(self, p_id):
        commit = get_pedersen_commit(p_id)
        if commit is None:
            print("Player has not published Pedersen commit yet.")
            return

        g = self.g
        p = self.p
        q = self.q
        h = self.h

        x = self.public_key_shares[p_id]
        (y, w, a, b, r) = commit
        #c = beacon(p_id, (x, y, w, a, b), q)
        c = tuple(beacon(self.party_id, (x,) + com, q) for com in zip(y, w, a, b))

        verfied = True
        for (y_i, w_i, a_i, b_i, r_i, c_i, h_i) in zip(y, w, a, b, r, c, h):
            test1 = (pow(g, r_i, p) == (a_i*pow(x, c_i, p)) % p)
            test2 = (pow(h_i, r_i, p) == (b_i*pow(y_i, c_i, p)) % p)

            if not (test1 and test2):
                print(test1, test2)
                print(self.party_id, "could not log ZKP verify", p_id)
                verfied = False
                break
            else:
                print(self.party_id, "passed", p_id, "on log ZKP verification.")

        if verfied:
            self.pedersen_commits_verified[p_id] = True
            self.global_decrypt_shares[p_id] = y

    def log_ZKP_verify_all(self):
        for p_id in range(self.n):
            if p_id != self.party_id:
                self.log_ZKP_verify(p_id)

    def decrypt(self):
        all_verified = reduce(and_, self.pedersen_commits_verified.values())
        if not all_verified:
            print("Haven't yet verified all other players. Aborting decryption.")
            return

        messages = []
        gds = list(self.global_decrypt_shares.values())

        for i in range(self.num_votes):
            l = [ds[i] for ds in gds]
            P = (prod(l) * self.decrypt_shares[i]) % self.p
            m = mod_div(self.ciphertexts[i][1], P, self.p) # TODO: check q
            messages.append(m)

        return messages


## The following would be on the server, represents the public bulletin board ##
voter_commits = {}
def publish_vote(p_id, commit):
    #assert len(commit) == 10, "Commit should consist of 10 numbers."
    voter_commits[p_id] = (commit)

def get_voter_commits(p_id):
    if p_id in voter_commits:
        return voter_commits[p_id]
    else:
        return None

class Voter(Pedersen):
    def __init__(self, p, g, n, voter_id, options, generators):
        self.num_votes = len(options)
        super(Voter, self).__init__(p, g, n, voter_id, self.num_votes)
        self.voter_id = voter_id
        self.options = options
        self.generators = generators

        self.votes_verified = {p_id: False for p_id in range(n) if p_id != voter_id}
        self.global_votes = {}
        
        # these are defined such that the final decrypted value will be g^x
        # where x is the total # of yes's - no's
        #self.yes = self.g
        #self.no = pow(self.g, p-2, p) # multiplicative inverse of g, g^-1
        self.generator_inverses = tuple(pow(G, p-2, p) for G in self.generators) # multiplicative inverse of g, g^-1

    def set_vote(self, vote):
        for i, v in enumerate(vote):
            assert 0 <= v < self.options[i], "Not a valid vote."

        self.vote = vote
    
    def encrypt_and_prove(self):
        self.encrypted_vote = []
        #v = []

        # temporary, simplified method
        #v = self.no
        #if self.vote:
        #    v = self.yes

        #self.v = v

        #(alpha, w, r1, d1) = (randint(self.q) for x in range(4))


        # these are just for making it cleaner
        p = self.p
        q = self.q
        h = self.public_key
        #v = self.v

        commits = []

        for i, o in enumerate(self.options):
            alpha = randint(q) # this alpha value is our secret key

            v = self.vote[i]
            G = self.generators[v] # G is the generator which represents our vote

            w = tuple(randint(q) for i in range(o))
            d = [randint(q) for i in range(o)] # this is still mildy ineffecient
            r = [randint(q) for i in range(o)]

            x = pow(g, alpha, p) # x and y are our actual encrypted vote
            y = (pow(h, alpha, p)*G) % p
            self.encrypted_vote.append((x, y)) # this is our own encrypted vote

            
            #a1 = (pow(g, r1, p)*pow(x, d1, p)) % p
            #b1 = (pow(h, r1, p)*pow((y*v)%p, d1, p)) % p
            #a2 = pow(g, w, p)
            #b2 = pow(h, w, p)
            #if self.vote:
            #    commit0 = (x, y, a1, b1, a2, b2)
            #else:
            #    commit0 = (x, y, a2, b2, a1, b1)

            #reencrypted_y = tuple(y*G_i for G_i in self.generator_inverses)

            u = q - alpha

            X = (x,) * o
            Y = tuple(y*self.generator_inverses[i]%p for i in range(o))

            w = (u*d[v] + r[v]) % q

            a = [(pow(X[i], d[i], p)*pow(g, r[i], p)) % p for i in range(o)]
            b = [(pow(Y[i], d[i], p)*pow(h, r[i], p)) % p for i in range(o)]
            
            #for i in range(o):
            #    if i == v:
            #        a.append((pow(g, r_v, p)*pow(x, d[v], p)) % p)
            #        b.append((pow(h, r_v, p)*pow((y*v)%p, d[v], p)) % p)

            #    else:
            #        a.append(pow(g, w[i], p))
            #        b.append(pow(h, w[i], p))

            commit0 = ((x, y), X, Y, a, b)

            # done with the first part

            # This represents getting the random value from the verifier.
            # To keep the protocol non-interactive, this will just be a hash
            # that the prover can't control. This also solves the problem of
            # the malicious verifier.
            c = beacon(self.voter_id, commit0, q)

            #d2 = (c - d1) % q
            #r2 = (w - alpha*d2) % q
            #if self.vote:
            #    commit1 = (d1, d2, r1, r2)
            #else:
            #    commit1 = (d2, d1, r2, r1)

            # skip is the index we will skip and choose c for. Probably doesn't have to be random,
            # but it can't hurt...
            #skip = randint(o - 1)
            #if skip >= v:
            #    skip += 1
            
            old_d = d[v]
            old_r = r[v]

            d_sum = sum(d) - d[v]
            d[v] = (c - d_sum) % q

            r[v] = (w - u*d[v]) % q

            #r = [(w[i] - alpha*d[i]) % q if i != v else r_v for i in range(o)]

            
            new_r = (alpha*(old_d - d[v]) + old_r) % q
            r[v] = new_r

            commit1 = (d, r)

            commit = commit0 + commit1
            commits.append(commit)

        publish_vote(self.voter_id, commits)
        # done with the protocol

    def verify_vote(self, p_id):
        commits = get_voter_commits(p_id)
        if commits is None:
            print("Voter hasn't published full proof yet.")
            return

        #g = self.yes
        #g_i = self.no # stands for multiplicative inverse of g
        p = self.p
        g = self.g
        h = self.public_key

                #test1 = (c == (d1 + d2) % q) # TODO: is mod p necessary?
        #test2 = (a1 == (pow(g, r1, p)*pow(x, d1, p)) % p)
        #test3 = (b1 == (pow(h, r1, p)*pow((y*g)%p, d1, p)) % p)
        #test4 = (a2 == (pow(g, r2, p)*pow(x, d2, p)) % p)
        #test5 = (b2 == (pow(h, r2, p)*pow((y*g_i)%p, d2, p)) % p)

        for i, o in enumerate(self.options):
            ((x, y), X, Y, a, b, d, r) = commits[i]
            c = beacon(p_id, commits[i][:4], q) # the c value should be the hash of the first 4 values commited

            test0 = (c == sum(d) % q) # TODO: can make this more effecient
            
            verfied = True

            if not test0:
                print(p_id, "failed their verification on c = d1 + d2 ... ...really?")
                verified = False

            for j in range(o):
                #G = self.generator_inverses[i]
                test1 = a[j] == (pow(X[j], d[j], p)*pow(g, r[j], p) % p)
                test2 = b[j] == (pow(Y[j], d[j], p)*pow(h, r[j], p) % p)

                if not (test1 and test2):
                    verfied = False
                    print(p_id, "failed their verification on one of the a or b tests.", o, j)

                if not verfied:
                    break


            if not verfied:
                print(p_id, "failed their verification! Someone's cheating! Abort!!")
                break
            else:
                print(self.voter_id, "passed", p_id, "on voting verification.")
                self.votes_verified[p_id] = True

                if p_id not in self.global_votes:
                    self.global_votes[p_id] = []

                self.global_votes[p_id].append((x, y))

    def verify_vote_all(self):
        for v_id in range(self.n):
            if v_id != self.voter_id:
                self.verify_vote(v_id)

    def calc_vote_step1(self):
        all_verified = reduce(and_, self.votes_verified.values())
        if not all_verified:
            print("Haven't yet verified all other voters. Aborting vote calculation.")
            return

        self.global_votes[self.voter_id] = self.encrypted_vote

        ws = [] # holds each of the w values

        for i in range(self.num_votes):
            # include our own vote
            #self.global_votes[self.voter_id].append(self.encrypted_vote)

            # this step does the additive homomorphic encryption
            # it gives us (x_0*x_1*...*x_n, y_0*y_1*...y_n) for all w_i = (x_i, y_i)
            w = reduce(lambda x,y: (x[0]*y[0] % p, x[1]*y[1] % p), [self.global_votes[p_id][i] for p_id in range(self.n)])
            #w = (w[0]%p, w[1]%p) # make it mod p

            # w is now the encrypted value holding the result of the vote.
            ws.append(w)
            # We now want to decrypt it as a group, first step is publishing our
            # ZKP commit

        self.ws = ws
        
        self.log_ZKP_prove(ws)

    def calc_vote_step2(self):
        self.log_ZKP_verify_all()
        # We should now be able to decrypt the value if all verifications are good

        out = self.decrypt()
        self.out = out
        return out


def test():
    #Testing Pederson public generation, zero knowledge proofs, and decryption
    p = int("FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF", 16)

    #p = 7
    q = (p-1)//2
    g = 2

    generators = [2, 4, 8, 16]
    num_voters = 3
    options = [4, 4, 4]
    votes = [[0, 3, 2], [0, 1, 2], [3, 1, 1]]
    voters = [Voter(p, g, num_voters, x, options, generators) for x in range(num_voters)]

    for vt in voters:
        vt.make_public_key()

    pk = voters[0].public_key
    s = sum(vt.secret for vt in voters) % q
    for vt in voters:
        assert pk == vt.public_key, "Differing public keys"

    assert pk == prod(vt.public_key_share for vt in voters) % p
    assert pk == pow(g, s, p) % p

    for vt in voters:
        vt.set_vote(votes[vt.voter_id])

    for vt in voters:
        vt.encrypt_and_prove()

    for vt in voters:
        vt.verify_vote_all()
        
    for vt in voters:
        vt.calc_vote_step1()

    outs = []
    ws_base = voters[0].ws
    for vt in voters:
        outs.append(vt.calc_vote_step2())

        assert vt.ws == ws_base, "hi..."

    out = outs[0]
    for o in outs:
        assert o == out, "Decryption resulted in different values"
        pass



    print("Election result:", out)

    expected_out = [prod(generators[v[i]] for v in votes) for i in range(len(options))]

    print("Expected result:", expected_out)

    assert out == expected_out, "Bad out"
    print("Success!")


