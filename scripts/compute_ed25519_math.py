from sympy.ntheory import sqrt_mod

P = (1 << 255) - 19
Q = (1 << 252) + 27742317777372353535851937790883648493

d = (-121665 * pow(121666, -1, P)) % P # twisted edwards form coefficient d

A = 486662 # montgomery form coefficient A
ed_to_mont_coef = sqrt_mod(-A - 2, P)

a = (3 - A * A) * pow(3, -1, P) % P  # weierstrass form coefficient a
b = (2 * A * A * A - 9 * A) * pow(27, -1, P) % P  # weierstrass form coefficient b

gx_ed = 0x216936D3CD6E53FEC0A4E231FDD6DC5C692CC7609525A7B2C9562D608F25D51A
gy_ed = 0x6666666666666666666666666666666666666666666666666666666666666658

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
    # assert verify_ed(x, y)
    x_mont, y_mont = ed_to_mont(x, y)
    x_weier, y_weier = mont_to_weier(x_mont, y_mont)
    # assert verify_weier(x_weier, y_weier)
    return x_weier, y_weier

gx, gy = ed_to_weier(gx_ed, gy_ed)

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

def fr(x):
    if type(x) is not list:
        x = to_chunks(x)
    print(f'''if (n == 64 && k == 4) {{
        ret[0] = {x[0]};
        ret[1] = {x[1]};
        ret[2] = {x[2]};
        ret[3] = {x[3]};
    }}''')