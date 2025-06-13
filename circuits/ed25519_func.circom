pragma circom 2.0.2;

// from https://github.com/ethereum/py_ecc/blob/master/py_ecc/secp256k1/secp256k1.py
// function get_gx(n, k) {
//     assert(n == 86 && k == 3);
//     var ret[100];
//     if (n == 86 && k == 3) {
//         ret[0] = 17117865558768631194064792;
//         ret[1] = 12501176021340589225372855;
//         ret[2] = 9198697782662356105779718;
//     }
//     return ret;
// }

// function get_gy(n, k) {
//     assert(n == 86 && k == 3);
//     var ret[100];
//     if (n == 86 && k == 3) {
//         ret[0] = 6441780312434748884571320;
//         ret[1] = 57953919405111227542741658;
//         ret[2] = 5457536640262350763842127;
//     }
//     return ret;
// }

// function get_secp256k1_prime(n, k) { // TODO: change to correct prime
//      assert((n == 86 && k == 3) || (n == 64 && k == 4));
//      var ret[100];
//      if (n == 86 && k == 3) {
//          ret[0] = 77371252455336262886226991;
//          ret[1] = 77371252455336267181195263;
//          ret[2] = 19342813113834066795298815;
//      }
//      if (n == 64 && k == 4) {
//          ret[0] = 18446744069414583343;
//          ret[1] = 18446744073709551615;
//          ret[2] = 18446744073709551615;
//          ret[3] = 18446744073709551615;
//      }
//      return ret;
// }

//TODO
function get_ec25519_prime(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 18446744073709551597;
        ret[1] = 18446744073709551615;
        ret[2] = 18446744073709551615;
        ret[3] = 9223372036854775807;
    }
    return ret;
}

function get_ec25519_order(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 6346243789798364141;
        ret[1] = 1503914060200516822;
        ret[2] = 0;
        ret[3] = 1152921504606846976;
    }
    return ret;
}

function get_ec25519_a(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 12297829303526400324;
        ret[1] = 12297829382473034410;
        ret[2] = 12297829382473034410;
        ret[3] = 3074457345618258602;
    }
    return ret;
}

function get_ec25519_b(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 2741388824290576484;
        ret[1] = 17080318586768103348;
        ret[2] = 683212743470724133;
        ret[3] = 8881765665119413741;
    }
    return ret;
}

// returns G * 2 ** 255
// TODO check that this is correct...
// TODO update for ed25519, as needed
function get_dummy_point(n, k) {
    assert(n == 86 && k == 3 || n == 64 && k == 4);
    var ret[2][100]; // should be [2][k]
    if (k == 3) {
        ret[0][0] = 34318960048412842733519232;
        ret[0][1] = 3417427387252098100392906;
        ret[0][2] = 2056756886390887154635856;
        ret[1][0] = 35848273954982567597050105;
        ret[1][1] = 74802087901123421621824957;
        ret[1][2] = 4851915413831746153124691;
    } else {
        ret[0][0] = 10184385086782357888;
        ret[0][1] = 16068507144229249874;
        ret[0][2] = 17097072337414981695;
        ret[0][3] = 1961476217642676500;
        ret[1][0] = 15220267994978715897;
        ret[1][1] = 2812694141792528170;
        ret[1][2] = 9886878341545582154;
        ret[1][3] = 4627147115546938088;
    }
    return ret;
}

// a[0], a[1] = x1, y1
// b[0], b[1] = x2, y2
// lamb = (b[1] - a[1]) / (b[0] - a[0]) % p
// out[0] = lamb ** 2 - a[0] - b[0] % p
// out[1] = lamb * (a[0] - out[0]) - a[1] % p
function ec25519_addunequal_func(n, k, x1, y1, x2, y2){
    var a[2][100];
    var b[2][100];

    for(var i = 0; i < k; i++){
        a[0][i] = x1[i];
        a[1][i] = y1[i];
        b[0][i] = x2[i];
        b[1][i] = y2[i];
    }

    var out[2][100];

    var p[100] = get_ec25519_prime(n, k);

    // b[1] - a[1]
    var sub1_out[100] = long_sub_mod_p(n, k, b[1], a[1], p);

    // b[0] - a[0]
    var sub0_out[100]= long_sub_mod_p(n, k, b[0], a[0], p);

    // lambda = (b[1] - a[1]) * inv(b[0] - a[0])
    var sub0inv[100] = mod_inv(n, k, sub0_out, p);
    var lambda[100] = prod_mod_p(n, k, sub1_out, sub0inv, p);

    // out[0] = lambda ** 2 - a[0] - b[0]
    var lambdasq_out[100] = prod_mod_p(n, k, lambda, lambda, p);
    var out0_pre_out[100] = long_sub_mod_p(n, k, lambdasq_out, a[0], p);
    var out0_out[100] = long_sub_mod_p(n, k, out0_pre_out, b[0], p);
    for (var i = 0; i < k; i++) {
        out[0][i] = out0_out[i];
    }

    // out[1] = lambda * (a[0] - out[0]) - a[1]
    var out1_0_out[100] = long_sub_mod_p(n, k, a[0], out[0], p);
    var out1_1_out[100] = prod_mod_p(n, k, lambda, out1_0_out, p);
    var out1_out[100] = long_sub_mod_p(n, k, out1_1_out, a[1], p);
    for (var i = 0; i < k; i++) {
        out[1][i] = out1_out[i];
    }

    return out;
}

// a[0], a[1] = x1, y1
// lamb = (3 * a[0] ** 2 + a_ell) / (2 * a[1]) % p
// out[0] = lamb ** 2 - (2 * a[0]) % p
// out[1] = lamb * (a[0] - out[0]) - a[1] % p
function ec25519_double_func(n, k, x1, y1){
    var a[2][100];
    var b[2][100];

    for(var i = 0; i < k; i++){
        a[0][i] = x1[i];
        a[1][i] = y1[i];
    }

    var out[2][100];

    var p[100] = get_ec25519_prime(n, k);
    var a_ell[100] = get_ec25519_a(n, k);

    // lamb_numer = 3 * a[0] ** 2
    var x1_sq[100] = prod_mod_p(n, k, a[0], a[0], p);
    var three[100];
    for (var i = 0; i < 100; i++) three[i] = i == 0 ? 3 : 0;
    var lamb_numer_temp[100] = prod_mod_p(n, k, x1_sq, three, p);
    var lamb_numer[100];
    for (var i = 0; i < 100; i++) { lamb_numer[i] = a_ell[i] + lamb_numer_temp[i]; }

    // lamb_denom = 2 * a[1]
    var two[100];
    for (var i = 0; i < 100; i++) two[i] = i == 0 ? 2 : 0;
    var lamb_denom[100] = prod_mod_p(n, k, a[1], two, p);

    // lambda = lamb_numer * inv(lamb_denom)
    var lamb_denom_inv[100] = mod_inv(n, k, lamb_denom, p);
    var lambda[100] = prod_mod_p(n, k, lamb_numer, lamb_denom_inv, p);

    // out[0] = lambda ** 2 - 2 * a[0]
    var lambdasq_out[100] = prod_mod_p(n, k, lambda, lambda, p);
    var out0_pre_out[100] = long_sub_mod_p(n, k, lambdasq_out, a[0], p);
    var out0_out[100] = long_sub_mod_p(n, k, out0_pre_out, a[0], p);
    for (var i = 0; i < k; i++) {
        out[0][i] = out0_out[i];
    }

    // out[1] = lambda * (a[0] - out[0]) - a[1]
    var out1_0_out[100] = long_sub_mod_p(n, k, a[0], out[0], p);
    var out1_1_out[100] = prod_mod_p(n, k, lambda, out1_0_out, p);
    var out1_out[100] = long_sub_mod_p(n, k, out1_1_out, a[1], p);
    for (var i = 0; i < k; i++) {
        out[1][i] = out1_out[i];
    }

    return out;
}
