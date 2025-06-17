from sympy.ntheory import sqrt_mod

P = (1 << 255) - 19
Q = (1 << 252) + 27742317777372353535851937790883648493
assert Q == (1 << 252) + 0x14def9dea2f79cd65812631a5cf5d3ed
jubjub = 21888242871839275222246405745257275088548364400416034343698204186575808495617

d = (-121665 * pow(121666, -1, P)) % P # twisted edwards form coefficient d

A = 486662 # montgomery form coefficient A
ed_to_mont_coef = sqrt_mod(-A - 2, P)
# assert ed_to_mont_coef == 6853475219497561581579357271197624642482790079785650197046958215289687604742

a = (3 - A * A) * pow(3, -1, P) % P  # weierstrass form coefficient a
b = (2 * A * A * A - 9 * A) * pow(27, -1, P) % P  # weierstrass form coefficient b

gx_ed = 0x216936D3CD6E53FEC0A4E231FDD6DC5C692CC7609525A7B2C9562D608F25D51A
gy_ed = 0x6666666666666666666666666666666666666666666666666666666666666658

assert gx_ed == 15112221349535400772501151409588531511454012693041857206046113283949847762202
assert gy_ed == 46316835694926478169428394003475163141307993866256225615783033603165251855960

def verify_ed(x, y):
    """Verify if the point (x, y) in twisted edwards form is on the ed25519 curve."""
    return (y * y - x * x - 1 - d * x * x * y * y) % P == 0

assert verify_ed(gx_ed, gy_ed)

def verify_mont(x, y):
    """Verify if the point (x, y) in montgomery form is on the ed25519 curve."""
    return (y * y - x * x * x - A * x * x - x) % P == 0

def verify_weier(x, y):
    """Verify if the point (x, y) in weierstrass form is on the ed25519 curve."""
    return (y * y - x * x * x - a * x - b) % P == 0

def ed_to_mont(x, y):
    """Convert a point from twisted edwards form to montgomery form."""
    assert verify_ed(x, y)
    x_mont = (1 + y) * pow(1 - y, -1, P) % P
    y_mont = ed_to_mont_coef * x_mont * pow(x, -1, P) % P
    assert verify_mont(x_mont, y_mont), (x_mont, y_mont)
    return x_mont, y_mont

def mont_to_weier(x, y):
    """Convert a point from montgomery form to weierstrass form."""
    assert verify_mont(x, y)
    x_weier = (x + A * pow(3, -1, P)) % P
    y_weier = y
    assert verify_weier(x_weier, y_weier), (x_weier, y_weier)
    return x_weier, y_weier

def ed_to_weier(x, y):
    """Convert a point from twisted edwards form to weierstrass form."""
    x_mont, y_mont = ed_to_mont(x, y)
    x_weier, y_weier = mont_to_weier(x_mont, y_mont)
    return x_weier, y_weier

gx_mont, gy_mont = ed_to_mont(gx_ed, gy_ed)
if gy_mont != 14781619447589544791020593568409986887264606134616475288964881837755586237401:
    ed_to_mont_coef = - ed_to_mont_coef
gx_mont, gy_mont = ed_to_mont(gx_ed, gy_ed)
assert gy_mont == 14781619447589544791020593568409986887264606134616475288964881837755586237401
gx, gy = ed_to_weier(gx_ed, gy_ed)
gp = [gx, gy]

def to_chunks(x, n=64, k=4):
    ans = []
    for _ in range(k):
        ans.append(x & ((1 << n) - 1))
        x >>= n
    assert not x
    return ans

def from_chunks(chunks, n=64, k=4):
    ans = 0
    for y in reversed(chunks):
        ans <<= n
        ans |= y
    return ans

fc = from_chunks

def fr(x):
    if type(x) is not list:
        x = to_chunks(x)
    print(f'''if (n == 64 && k == 4) {{
        ret[0] = {x[0]};
        ret[1] = {x[1]};
        ret[2] = {x[2]};
        ret[3] = {x[3]};
    }}''')

def ec_add(p1, p2):
    if p1 == p2:
        return ec_double(p1)
    x1, y1 = p1
    x2, y2 = p2
    lamb = ((y2 - y1) * pow(x2 - x1, -1, P)) % P
    x3 = (lamb * lamb - x1 - x2) % P
    y3 = (lamb * (x1 - x3) - y1) % P
    assert verify_weier(x3, y3), (x3, y3)
    return [x3, y3]

def ec_double(p):
    x, y = p
    assert y != 0, (x, y)
    lamb = ((3 * x * x + a) * pow(2 * y, -1, P)) % P
    x3 = (lamb * lamb - 2 * x) % P
    y3 = (lamb * (x - x3) - y) % P
    assert verify_weier(x3, y3), (x3, y3)
    return [x3, y3]

def gen_powers():
    stride = 8
    num_strides = 32
    powers = [[[0, 0] for _ in range(1 << stride)] for _ in range(num_strides)]

    # powers[j][i] = [j * 2**(stride * i) * g]
    for i in range(num_strides):
        for j in range(1, 1 << stride):
            if i == 0 and j == 1:
                powers[i][j] = [gx, gy]
            elif j == 1:
                p = powers[i - 1][1]
                for _ in range(stride):
                    p = ec_double(p)
                powers[i][j] = p
            else:
                powers[i][j] = ec_add(powers[i][1], powers[i][j - 1])

    for i in range(num_strides):
        for j in range(1, 1 << stride):
            for k in range(2):
                powers[i][j][k] = to_chunks(powers[i][j][k])

    return powers

def generate_ed25519_powers_circom():
    """Generate the Ed25519 powers table in Circom format."""
    powers = gen_powers()
    
    with open('../circuits/ed25519_g_pow_stride8_table.circom', 'w') as f:
        f.write('pragma circom 2.0.2;\n\n')
        f.write('function get_ed25519_g_pow_stride8_table(n, k) {\n')
        f.write('    assert(n == 64 && k == 4);\n')
        f.write('    var powers[32][256][2][4];\n\n')
        
        for i in range(32):
            for j in range(256):
                for coord in range(2):  # 0 for x, 1 for y
                    if j == 0:
                        # Point at infinity
                        for chunk in range(4):
                            f.write(f'    powers[{i}][{j}][{coord}][{chunk}] = 0;\n')
                    else:
                        for chunk in range(4):
                            value = powers[i][j][coord][chunk]
                            f.write(f'    powers[{i}][{j}][{coord}][{chunk}] = {value};\n')
                
                if j < 255 or i < 31:  # Add blank line between points except at the very end
                    f.write('\n')
        
        f.write('    return powers;\n')
        f.write('}\n')
    
    print("Generated ../circuits/ed25519_g_pow_stride8_table.circom")

def bin_exp(a, n, mul, one=None):
    '''computes a^n, where multiplication operation is defined by 
    mul and one is the identity element. n must be nonnegative'''
    ans = one
    while n:
        if n & 1:
            if ans is None:
                ans = a
            else:
                ans = mul(ans, a)
        a = mul(a, a)
        n >>= 1
    return ans

def scalar_mul(scalar, p):
    """Computes scalar * p using double-and-add algorithm."""
    return bin_exp(p, scalar, ec_add)

def tcs(x):
    if type(x) is list:
        return list(map(tcs, x))
    return list(map(str, to_chunks(x)))

def gen_test_case(r, m, a):
    s = (r + m * a) % Q
    R = scalar_mul(r, gp)
    A = scalar_mul(a, gp)
    assert scalar_mul(s, gp) == ec_add(R, scalar_mul(m, A))
    return {
        's': tcs(s),
        'R': tcs(R),
        'm': tcs(m),
        'A': tcs(A)
    }

def gen_rand_test_case():
    import random
    r = random.randint(1, Q - 1)
    m = random.randint(1, Q - 1)
    a = random.randint(1, Q - 1)
    return gen_test_case(r, m, a)

y1 = [15460636801924274383, 5045058846054993547, 6033304802971312003, 3158272936523719135]
x3 = [7877567957821876018, 16298599610961404402, 12413439270738239612, 15288471137185832480, 9223372036854775807]
ny1 = [21888242871839275222246405745257275088548364400416034343682743549773884221234, 21888242871839275222246405745257275088548364400416034343693159127729753502070, 21888242871839275222246405745257275088548364400416034343692170881772837183614, 21888242871839275222246405745257275088548364400416034343695045913639284776482]