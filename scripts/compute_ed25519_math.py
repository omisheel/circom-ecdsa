P = (1 << 255) - 19

d = (-121665 * pow(121666, -1, P)) % P # twisted edwards form coefficient d

A = 486662 # montgomery form coefficient A

a = (3 - A * A) * pow(3, -1, P) % P  # weierstrass form coefficient a
b = (2 * A * A * A - 9 * A) * pow(27, -1, P) % P  # weierstrass form coefficient b

def verify_ed(x, y):
    """Verify if the point (x, y) in twisted edwards form is on the ed25519 curve."""
    return (y * y - x * x - 1 - d * x * x * y * y) % P == 0

def verify_mont(x, y):
    """Verify if the point (x, y) in montgomery form is on the ed25519 curve."""
    return (y * y - x * x * x - A * x * x - y) % P == 0

def verify_weier(x, y):
    """Verify if the point (x, y) in weierstrass form is on the ed25519 curve."""
    return (y * y - x * x * x - a * x - b) % P == 0

def ed_to_mont(x, y):
    """Convert a point from twisted edwards form to montgomery form."""
    assert verify_ed(x, y)
    x_mont = (1 + y) * pow(1 - y, -1, P) % P
    y_mont = x_mont * pow(x, -1, P) % P
    assert verify_mont(x_mont, y_mont)
    return x_mont, y_mont

def mont_to_weier(x, y):
    """Convert a point from montgomery form to weierstrass form."""
    assert verify_mont(x, y)
    x_weier = (x - A * pow(3, -1, P)) % P
    y_weier = y
    assert verify_weier(x_weier, y_weier)
    return x_weier, y_weier

def ed_to_weier(x, y):
    """Convert a point from twisted edwards form to weierstrass form."""
    assert verify_ed(x, y)
    x_mont, y_mont = ed_to_mont(x, y)
    x_weier, y_weier = mont_to_weier(x_mont, y_mont)
    assert verify_weier(x_weier, y_weier)
    return x_weier, y_weier

def to_chunks(x, n=64, k=4):
    ans = []
    for _ in range(k):
        ans.append(x & ((1 << n) - 1))
        x >>= n
    assert not x
    return ans