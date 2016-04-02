from functools import reduce
import random

def prod(iterable):
    return reduce(lambda x,y: x*y, iterable)

p = int("FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF", 16)
q = (p-1)//2
g = 2

#n = 3 # number of parties
#my_id = 0 # id of this party

def randint(r):
    return random.SystemRandom().randint(0, r-1)

def mod_div(n, d, m):
    inverse = pow(d, m-2, m)
    return (n*inverse) % m

def gen_poly(n, q):
    """Returns a polynomial mod q of degree n-1."""
    poly = [randint(q) for x in range(n)]
    return poly

def eval_poly(poly, x, q):
    """Returns the polynomial evaluated at x."""
    deg = len(poly)
    y = sum(c*pow(x, p, q) for c, p in zip(poly, range(deg))) % q
    return y


def lagrange(x, y, G):
    assert len(x) == len(y) and len(x) > 0, "Lengths of x and y must equal and non-zero."
    x_len = len(x)
    f = [0] * x_len
    for i in range(x_len):
        partial = []
        combo_list = list(x)
        combo_list.pop(i)
        for j in range(x_len):
            c = 0
            for k in combinations(combo_list, j):
                c += prod(map(lambda q: -q, k), G)
            partial.append(c)
        d = 1
        for j in range(x_len):
            if j != i:
                d = (d * (x[i] - x[j]))

        partial = map(lambda q: div(mul(q, y[i]),  d), partial) # fix this babe
        f = [(m + n) % G for m, n in zip(f, partial)] # also needs % G


def elgamal_encrypt(message, public_key, g, q):
    m = pow(g, message, p) # TODO: pretty sure about this p (and the next few) but not totally sure
    r = randint(q)
    x = pow(g, r, p)
    y = (pow(public_key, r, p) * m) % p
    return (x, y)




class Player:
    def __init__(self, n, party_id): # TODO: deal with q and g and p
        assert 0 <= party_id < n, "ID must be less than n."
        self.n = n
        self.party_id = party_id
        self.global_shares = {}
        self.public_key_shares = {}
        self.proofs = {}
        self.c_values = {}
        self.r_values = {}

        self.poly = gen_poly(n, q)
        self.secret = self.poly[0] # poly(0) is our secret part of the public key
        self.public_key_share = pow(g, self.secret, p) # TODO: make sure this is p

        self.shares = {} # format is {p_id: (share, commit)}
        for p_id in range(n):
            if p_id != self.party_id: # we don't publish our own share
                share = eval_poly(self.poly, p_id+1, q)
                commit = pow(g, share, p) # g^share mod p is the verifiable commit
                self.shares[p_id] = (share, commit)
        

    def publish_shares(self):
        return self.shares

    def publish_public_key_share(self):
        return self.public_key_share

    def receive_share(self, p_id, share):
        """In this case p_id is the ID of the party we are receiving from"""
        self.global_shares[p_id] = share

    def receive_public_key_share(self, p_id, share):
        self.public_key_shares[p_id] = share

    def sum_shares(self):
        assert len(self.global_shares) == self.n-1, "Have not received all shares."
        assert len(self.public_key_shares) == self.n-1, "Have not received all shares."
        self.global_share = sum(x[0] for x in self.global_shares.values())
        
        # We now have every commit
        m = prod(self.public_key_shares.values())
        self.public_key = (m * self.public_key_share) % p

    
    def log_ZKP_prove_step1(self, ciphertext):
        self.ciphertext = ciphertext
        x = ciphertext[0]
        y = ciphertext[1]

        # w is our share of the decrypted ciphertext
        w = pow(x, self.secret, p) # TODO: is this mod p or q?
        self.w = w # we need w for decription later and for step 2

        # We now need to prove that log_g(self.public_key_share) == log_x(w)
        # or, in other words, we haven't changed our secret when calculating w
        # This is done using the zero knowledge proof from Pedersen
        r = randint(q)
        self.random_w = r
        a = pow(g, r, p) # TODO: are these mod q?
        b = pow(x, r, p)
        self.a = a # these are unnecessary to keep
        self.b = b

        return [w, a, b] # now anyone should be able to verify that w is #legit

    def log_ZKP_verify_step2_receive(self, p_id, proof):
        proof.append(randint(q)) # the c value
        self.proofs[p_id] = proof

    def log_ZKP_verify_step2_send(self):
        assert len(self.proofs) == self.n-1, "Haven't received all proofs yet."
        tests = {p_id: proof[3] for p_id, proof in self.proofs.items()}
        return tests

    def log_ZKP_prove_step3_receive(self, p_id, c):
        self.c_values[p_id] = c

    def log_ZKP_prove_step3_send(self):
        assert len(self.c_values) == self.n-1, "Haven't received all c values yet."
        print("c", c)
        r = {p_id: (self.random_w + c*self.secret) for p_id, c in self.c_values.items()} # TODO: mod q????
        self.r = r
        return r

    def log_ZKP_verify_step4_receive(self, p_id, r):
        self.r_values[p_id] = r

    def log_ZKP_verify_step4_verify(self):
        assert len(self.r_values) == self.n-1, "Haven't received all r values yet."

        abort = False
        for p_id in range(self.n):
            if p_id != self.party_id:
                r = self.r_values[p_id]
                a = self.proofs[p_id][1]
                x = self.public_key_shares[p_id]
                c = self.proofs[p_id][3] #self.c_values[p_id]
                h = self.ciphertext[0]
                b = self.proofs[p_id][2]
                y = self.proofs[p_id][0]

                test1 = (pow(g, r, p) == (a*pow(x, c, p)) % p)
                test2 = (pow(h, r, p) == (b*pow(y, c, p)) % p)

                if not (test1 and test2):
                    print(test1, test2)
                    abort = True
                    print(self.party_id, "Uh oh!", p_id, "failed their ZKP. Abort!!!!")
                else:
                    print("All tests passed!")

        self.abort = abort

    def log_ZKP_self_test(self):
        h = self.ciphertext[0] # the x from the ciphertext
        x = self.public_key_share
        y = pow(h, self.secret, p)

        w = randint(q)
        (a, b) = (pow(g, w, p), pow(h, w, p))

        c = randint(q)

        r = w + self.secret*c

        assert pow(g, r, p) == (a*pow(x, c, p))%p, "Self test1 failed."
        assert pow(h, r, p) == (b*pow(y, c, p))%p, "Self test2 failed."
        print("Tests passed.")

    def decrypt(self):
        #assert not self.abort, "ZKPs were not completed successfully. Decrypt is dangerous."
        #print(self.proofs)

        w = map(lambda x: x[0], self.proofs.values())
        P = prod(w) * self.w
        message = mod_div(self.ciphertext[1], P, p) # TODO: check q

        return message


num_players = 10
players = [Player(num_players, x) for x in range(num_players)]

for player in players:
    s = player.publish_shares()
    for p_id,share in s.items():
        players[p_id].receive_share(player.party_id, share)
        

for p_id in range(num_players):
    pk_share = players[p_id].publish_public_key_share()
    for p_id2 in range(num_players):
        if p_id2 != p_id:
            players[p_id2].receive_public_key_share(p_id, pk_share)

for player in players:
    player.sum_shares()

pk = players[0].public_key
for player in players:
    assert pk == player.public_key, "Public key mismatch"

s = sum(pl.secret for pl in players)
assert pow(g, s, p) == pk, "Invalid elgamal keypair."

my_message = 23466434
ciphertext = elgamal_encrypt(my_message, pk, g, q)

for player in players:
    proof = player.log_ZKP_prove_step1(ciphertext)
    for p_id in range(num_players):
        if p_id != player.party_id:
            players[p_id].log_ZKP_verify_step2_receive(player.party_id, proof)

for player in players:
    sent = player.log_ZKP_verify_step2_send()
    for p_id,c in sent.items():
        players[p_id].log_ZKP_prove_step3_receive(player.party_id, c)

for player in players:
    sent = player.log_ZKP_prove_step3_send()
    for p_id,r in sent.items():
        players[p_id].log_ZKP_verify_step4_receive(player.party_id, r)

print("final c", c)
thingy = pow(g, my_message, p)
for player in players:
    player.log_ZKP_verify_step4_verify()
    assert thingy == player.decrypt()
