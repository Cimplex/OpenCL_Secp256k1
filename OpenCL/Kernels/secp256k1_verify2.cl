/* Limbs of the secp256k1 order. */
#define SECP256K1_N_0 ((ulong)0xBFD25E8CD0364141UL)
#define SECP256K1_N_1 ((ulong)0xBAAEDCE6AF48A03BUL)
#define SECP256K1_N_2 ((ulong)0xFFFFFFFFFFFFFFFEUL)
#define SECP256K1_N_3 ((ulong)0xFFFFFFFFFFFFFFFFUL)

/* Limbs of 2^256 minus the secp256k1 order. */
#define SECP256K1_N_C_0 (~SECP256K1_N_0 + 1)
#define SECP256K1_N_C_1 (~SECP256K1_N_1)
#define SECP256K1_N_C_2 (1)

/* Limbs of half the secp256k1 order. */
#define SECP256K1_N_H_0 ((ulong)0xDFE92F46681B20A0UL)
#define SECP256K1_N_H_1 ((ulong)0x5D576E7357A4501DUL)
#define SECP256K1_N_H_2 ((ulong)0xFFFFFFFFFFFFFFFFUL)
#define SECP256K1_N_H_3 ((ulong)0x7FFFFFFFFFFFFFFFUL)

/* Determine the number of trailing zero bits in a (non-zero) 64-bit x.
 * This function is only intended to be used as fallback for
 * secp256k1_ctz64_var, but permits it to be tested separately. */
__constant uchar debruijn[64] = {
	0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28,
	62, 5, 39, 46, 44, 42, 22, 9, 24, 35, 59, 56, 49, 18, 29, 11,
	63, 52, 6, 26, 37, 40, 33, 47, 61, 45, 43, 21, 23, 58, 17, 10,
	51, 25, 36, 32, 60, 20, 57, 16, 50, 31, 19, 15, 30, 14, 13, 12
};
static int secp256k1_ctz64_var_debruijn(ulong x) {
    return debruijn[(ulong)((x & -x) * 0x022FDD63CC95386DUL) >> 58];
}

/* int128 and uint128 implementation */
typedef struct { ulong hi; ulong lo; } secp256k1_uint128;
typedef struct { long hi; ulong lo; } secp256k1_int128;
static void secp256k1_u128_add(secp256k1_uint128 *r, const secp256k1_uint128 *a, const secp256k1_uint128 *b) {
    uchar carry;

    r->lo = a->lo + b->lo;
    carry = (r->lo < a->lo) || (r->lo < b->lo);

    r->hi = a->hi + b->hi + carry;
}
static void secp256k1_u128_mul(secp256k1_uint128 *r, ulong a, ulong b) {
    ulong lowPart = (ulong)a * (ulong)b;
	ulong highPart = mul_hi(a, b);

	r->lo = lowPart;
	r->hi = highPart;
}
static void secp256k1_u128_accum_u64(secp256k1_uint128 *r, ulong a) {
    uchar carry;
	r->lo = r->lo + a;
	carry = (r->lo < a);
	r->hi = r->hi + carry;
}
static void secp256k1_u128_accum_mul(secp256k1_uint128 *r, ulong a, ulong b) {
    secp256k1_uint128 ab;
    secp256k1_u128_mul(&ab, a, b);

    secp256k1_uint128 temp = *r;
    secp256k1_u128_add(&temp, &temp, &ab);
    *r = temp;
}

// NEEDS TESTING (negative carry)
static void secp256k1_i128_add(secp256k1_int128 *r, const secp256k1_int128 *a, const secp256k1_int128 *b) {
    uchar carry;

    r->lo = a->lo + b->lo;
    carry = (r->lo < a->lo) || (r->lo < b->lo);

    r->hi = a->hi + b->hi + carry;
}
static void secp256k1_i128_mul(secp256k1_int128 *r, long a, long b) {
    ulong lowPart = (ulong)a * (ulong)b;
	long highPart = mul_hi(a, b);

	r->lo = lowPart;
	r->hi = highPart;
}
static void secp256k1_i128_accum_mul(secp256k1_int128 *r, long a, long b) {
    secp256k1_int128 ab;
    secp256k1_i128_mul(&ab, a, b);

    secp256k1_int128 temp = *r;
    secp256k1_i128_add(&temp, &temp, &ab);
    *r = temp;
}

// NEEDS TESTING
static ulong secp256k1_i128_to_u64(const secp256k1_int128 *a) {
    return a->lo;
}

static void secp256k1_u128_from_u64(secp256k1_uint128 *r, ulong a) {
    r->lo = a;
}

// NEEDS TESTING (check negative)
static long secp256k1_i128_to_i64(const secp256k1_int128 *a) {
    return (long)a->lo;
}

static ulong secp256k1_u128_to_u64(const secp256k1_uint128 *a) {
   return a->lo;
}

// NEEDS TESTING
static void secp256k1_i128_rshift(secp256k1_int128 *r, unsigned int n) {
	r->hi >>= n;
	r->hi |= r->lo << (64 - n);
	r->lo >>= n;
}

// NEEDS TESTING (check negative)
static void secp256k1_u128_rshift(secp256k1_uint128 *r, unsigned int n) {
	r->hi >>= n;
	r->hi |= r->lo << (64 - n);
	r->lo >>= n;
}

// NEEDS TESTING
static ulong secp256k1_u128_hi_u64(const secp256k1_uint128 *a) {
   return a->hi;
}


/* A signed 62-bit limb representation of integers. Its value is sum(v[i] * 2^(62*i), i=0..4). */
typedef struct {
    long v[5];
} secp256k1_modinv64_signed62;
typedef struct {
    /* The modulus in signed62 notation, must be odd and in [3, 2^256]. */
    secp256k1_modinv64_signed62 modulus;
    ulong modulus_inv62; /* modulus^{-1} mod 2^62 */
} secp256k1_modinv64_modinfo;
__constant secp256k1_modinv64_modinfo secp256k1_const_modinfo_scalar = {
    {{0x3FD25E8CD0364141LL, 0x2ABB739ABD2280EELL, -0x15LL, 0, 256}},
    0x34F20099AA774EC1LL
};
typedef struct {
    long u, v, q, r;
} secp256k1_modinv64_trans2x2;
static long secp256k1_modinv64_divsteps_62_var(long eta, ulong f0, ulong g0, secp256k1_modinv64_trans2x2 *t) {
    ulong u = 1, v = 0, q = 0, r = 1;
    ulong f = f0, g = g0, m;
    uint w;
    int i = 62, limit, zeros;
    for (;;) {
        /* Use a sentinel bit to count zeros only up to i. */
        zeros = secp256k1_ctz64_var_debruijn(g | (ULONG_MAX << i));
        /* Perform zeros divsteps at once; they all just divide g by two. */
        g >>= zeros;
        u <<= zeros;
        v <<= zeros;
        eta -= zeros;
        i -= zeros;
        /* We're done once we've done 62 divsteps. */
        if (i == 0) break;
        /* If eta is negative, negate it and replace f,g with g,-f. */
        if (eta < 0) {
            ulong tmp;
            eta = -eta;
            tmp = f; f = g; g = -tmp;
            tmp = u; u = q; q = -tmp;
            tmp = v; v = r; r = -tmp;
            /* Use a formula to cancel out up to 6 bits of g. Also, no more than i can be cancelled
             * out (as we'd be done before that point), and no more than eta+1 can be done as its
             * sign will flip again once that happens. */
            limit = ((int)eta + 1) > i ? i : ((int)eta + 1);
            /* m is a mask for the bottom min(limit, 6) bits. */
            m = (ULONG_MAX >> (64 - limit)) & 63U;
            /* Find what multiple of f must be added to g to cancel its bottom min(limit, 6) bits. */
            w = (f * g * (f * f - 2)) & m;
        } else {
            /* In this branch, use a simpler formula that only lets us cancel up to 4 bits of g, as eta tends to be smaller here. */
            limit = ((int)eta + 1) > i ? i : ((int)eta + 1);
            /* m is a mask for the bottom min(limit, 4) bits. */
            m = (ULONG_MAX >> (64 - limit)) & 15U;
            /* Find what multiple of f must be added to g to cancel its bottom min(limit, 4) bits. */
            w = f + (((f + 1) & 4) << 1);
            w = (-w * g) & m;
        }
        g += f * w;
        q += u * w;
        r += v * w;
    }
    /* Return data in t and return value. */
    t->u = (long)u;
    t->v = (long)v;
    t->q = (long)q;
    t->r = (long)r;
    return eta;
}
static void secp256k1_modinv64_update_de_62(secp256k1_modinv64_signed62 *d, secp256k1_modinv64_signed62 *e, const secp256k1_modinv64_trans2x2 *t, __constant secp256k1_modinv64_modinfo* modinfo) {
    const ulong M62 = ULONG_MAX >> 2;
    const long d0 = d->v[0], d1 = d->v[1], d2 = d->v[2], d3 = d->v[3], d4 = d->v[4];
    const long e0 = e->v[0], e1 = e->v[1], e2 = e->v[2], e3 = e->v[3], e4 = e->v[4];
    const long u = t->u, v = t->v, q = t->q, r = t->r;
    long md, me, sd, se;
    secp256k1_int128 cd, ce;

    /* [md,me] start as zero; plus [u,q] if d is negative; plus [v,r] if e is negative. */
    sd = d4 >> 63;
    se = e4 >> 63;
    md = (u & sd) + (v & se);
    me = (q & sd) + (r & se);
    /* Begin computing t*[d,e]. */
    secp256k1_i128_mul(&cd, u, d0);
    secp256k1_i128_accum_mul(&cd, v, e0);
    secp256k1_i128_mul(&ce, q, d0);
    secp256k1_i128_accum_mul(&ce, r, e0);
    /* Correct md,me so that t*[d,e]+modulus*[md,me] has 62 zero bottom bits. */
    md -= (modinfo->modulus_inv62 * secp256k1_i128_to_u64(&cd) + md) & M62;
    me -= (modinfo->modulus_inv62 * secp256k1_i128_to_u64(&ce) + me) & M62;
    /* Update the beginning of computation for t*[d,e]+modulus*[md,me] now md,me are known. */
    secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[0], md);
    secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[0], me);
    /* Verify that the low 62 bits of the computation are indeed zero, and then throw them away. */
    secp256k1_i128_rshift(&cd, 62);
    secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 1 of t*[d,e]+modulus*[md,me], and store it as output limb 0 (= down shift). */
    secp256k1_i128_accum_mul(&cd, u, d1);
    secp256k1_i128_accum_mul(&cd, v, e1);
    secp256k1_i128_accum_mul(&ce, q, d1);
    secp256k1_i128_accum_mul(&ce, r, e1);
    if (modinfo->modulus.v[1]) { /* Optimize for the case where limb of modulus is zero. */
        secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[1], md);
        secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[1], me);
    }
    d->v[0] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[0] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 2 of t*[d,e]+modulus*[md,me], and store it as output limb 1. */
    secp256k1_i128_accum_mul(&cd, u, d2);
    secp256k1_i128_accum_mul(&cd, v, e2);
    secp256k1_i128_accum_mul(&ce, q, d2);
    secp256k1_i128_accum_mul(&ce, r, e2);
    if (modinfo->modulus.v[2]) { /* Optimize for the case where limb of modulus is zero. */
        secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[2], md);
        secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[2], me);
    }
    d->v[1] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[1] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 3 of t*[d,e]+modulus*[md,me], and store it as output limb 2. */
    secp256k1_i128_accum_mul(&cd, u, d3);
    secp256k1_i128_accum_mul(&cd, v, e3);
    secp256k1_i128_accum_mul(&ce, q, d3);
    secp256k1_i128_accum_mul(&ce, r, e3);
    if (modinfo->modulus.v[3]) { /* Optimize for the case where limb of modulus is zero. */
        secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[3], md);
        secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[3], me);
    }
    d->v[2] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[2] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 4 of t*[d,e]+modulus*[md,me], and store it as output limb 3. */
    secp256k1_i128_accum_mul(&cd, u, d4);
    secp256k1_i128_accum_mul(&cd, v, e4);
    secp256k1_i128_accum_mul(&ce, q, d4);
    secp256k1_i128_accum_mul(&ce, r, e4);
    secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[4], md);
    secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[4], me);
    d->v[3] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[3] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* What remains is limb 5 of t*[d,e]+modulus*[md,me]; store it as output limb 4. */
    d->v[4] = secp256k1_i128_to_i64(&cd);
    e->v[4] = secp256k1_i128_to_i64(&ce);
}
static void secp256k1_modinv64_update_fg_62_var(int len, secp256k1_modinv64_signed62 *f, secp256k1_modinv64_signed62 *g, const secp256k1_modinv64_trans2x2 *t) {
    const ulong M62 = ULONG_MAX >> 2;
    const long u = t->u, v = t->v, q = t->q, r = t->r;
    long fi, gi;
    secp256k1_int128 cf, cg;
    int i;
    /* Start computing t*[f,g]. */
    fi = f->v[0];
    gi = g->v[0];
    secp256k1_i128_mul(&cf, u, fi);
    secp256k1_i128_accum_mul(&cf, v, gi);
    secp256k1_i128_mul(&cg, q, fi);
    secp256k1_i128_accum_mul(&cg, r, gi);
    /* Verify that the bottom 62 bits of the result are zero, and then throw them away. */
    secp256k1_i128_rshift(&cf, 62);
    secp256k1_i128_rshift(&cg, 62);
    /* Now iteratively compute limb i=1..len of t*[f,g], and store them in output limb i-1 (shifting
     * down by 62 bits). */
    for (i = 1; i < len; ++i) {
        fi = f->v[i];
        gi = g->v[i];
        secp256k1_i128_accum_mul(&cf, u, fi);
        secp256k1_i128_accum_mul(&cf, v, gi);
        secp256k1_i128_accum_mul(&cg, q, fi);
        secp256k1_i128_accum_mul(&cg, r, gi);
        f->v[i - 1] = secp256k1_i128_to_u64(&cf) & M62; secp256k1_i128_rshift(&cf, 62);
        g->v[i - 1] = secp256k1_i128_to_u64(&cg) & M62; secp256k1_i128_rshift(&cg, 62);
    }
    /* What remains is limb (len) of t*[f,g]; store it as output limb (len-1). */
    f->v[len - 1] = secp256k1_i128_to_i64(&cf);
    g->v[len - 1] = secp256k1_i128_to_i64(&cg);
}
static void secp256k1_modinv64_normalize_62(secp256k1_modinv64_signed62 *r, long sign, __constant secp256k1_modinv64_modinfo *modinfo) {
    const long M62 = (long)(ULONG_MAX >> 2);
    long r0 = r->v[0], r1 = r->v[1], r2 = r->v[2], r3 = r->v[3], r4 = r->v[4];
    
	// NEEDS TESTING, remove volatile keyword
	long cond_add, cond_negate;

    /* In a first step, add the modulus if the input is negative, and then negate if requested.
     * This brings r from range (-2*modulus,modulus) to range (-modulus,modulus). As all input
     * limbs are in range (-2^62,2^62), this cannot overflow an int64_t. Note that the right
     * shifts below are signed sign-extending shifts (see assumptions.h for tests that that is
     * indeed the behavior of the right shift operator). */
    cond_add = r4 >> 63;
    r0 += modinfo->modulus.v[0] & cond_add;
    r1 += modinfo->modulus.v[1] & cond_add;
    r2 += modinfo->modulus.v[2] & cond_add;
    r3 += modinfo->modulus.v[3] & cond_add;
    r4 += modinfo->modulus.v[4] & cond_add;
    cond_negate = sign >> 63;
    r0 = (r0 ^ cond_negate) - cond_negate;
    r1 = (r1 ^ cond_negate) - cond_negate;
    r2 = (r2 ^ cond_negate) - cond_negate;
    r3 = (r3 ^ cond_negate) - cond_negate;
    r4 = (r4 ^ cond_negate) - cond_negate;
    /* Propagate the top bits, to bring limbs back to range (-2^62,2^62). */
    r1 += r0 >> 62; r0 &= M62;
    r2 += r1 >> 62; r1 &= M62;
    r3 += r2 >> 62; r2 &= M62;
    r4 += r3 >> 62; r3 &= M62;

    /* In a second step add the modulus again if the result is still negative, bringing
     * r to range [0,modulus). */
    cond_add = r4 >> 63;
    r0 += modinfo->modulus.v[0] & cond_add;
    r1 += modinfo->modulus.v[1] & cond_add;
    r2 += modinfo->modulus.v[2] & cond_add;
    r3 += modinfo->modulus.v[3] & cond_add;
    r4 += modinfo->modulus.v[4] & cond_add;
    /* And propagate again. */
    r1 += r0 >> 62; r0 &= M62;
    r2 += r1 >> 62; r1 &= M62;
    r3 += r2 >> 62; r2 &= M62;
    r4 += r3 >> 62; r3 &= M62;

    r->v[0] = r0;
    r->v[1] = r1;
    r->v[2] = r2;
    r->v[3] = r3;
    r->v[4] = r4;
}
static void secp256k1_modinv64_var(secp256k1_modinv64_signed62 *x, __constant secp256k1_modinv64_modinfo *modinfo) {
    /* Start with d=0, e=1, f=modulus, g=x, eta=-1. */
    secp256k1_modinv64_signed62 d = {{0, 0, 0, 0, 0}};
    secp256k1_modinv64_signed62 e = {{1, 0, 0, 0, 0}};
    secp256k1_modinv64_signed62 f = modinfo->modulus;
    secp256k1_modinv64_signed62 g = *x;

    int j, len = 5;
    ulong eta = -1; /* eta = -delta; delta is initially 1 */
    ulong cond, fn, gn;

    /* Do iterations of 62 divsteps each until g=0. */
    while (1) {
        /* Compute transition matrix and new eta after 62 divsteps. */
        secp256k1_modinv64_trans2x2 t;
        eta = secp256k1_modinv64_divsteps_62_var(eta, f.v[0], g.v[0], &t);
        /* Update d,e using that transition matrix. */
        secp256k1_modinv64_update_de_62(&d, &e, &t, modinfo);
        /* Update f,g using that transition matrix. */
        secp256k1_modinv64_update_fg_62_var(len, &f, &g, &t);
        /* If the bottom limb of g is zero, there is a chance that g=0. */
        if (g.v[0] == 0) {
            cond = 0;
            /* Check if the other limbs are also 0. */
            for (j = 1; j < len; ++j) {
                cond |= g.v[j];
            }
            /* If so, we're done. */
            if (cond == 0) break;
        }

        /* Determine if len>1 and limb (len-1) of both f and g is 0 or -1. */
        fn = f.v[len - 1];
        gn = g.v[len - 1];
        cond = ((long)len - 2) >> 63;
        cond |= fn ^ (fn >> 63);
        cond |= gn ^ (gn >> 63);
        /* If so, reduce length, propagating the sign of f and g's top limb into the one below. */
        if (cond == 0) {
            f.v[len - 2] |= (ulong)fn << 62;
            g.v[len - 2] |= (ulong)gn << 62;
            --len;
        }
    }

    /* Optionally negate d, normalize to [0,modulus), and return it. */
    secp256k1_modinv64_normalize_62(&d, f.v[len - 1], modinfo);
    *x = d;
}

/** This field implementation represents the value as 5 ulong limbs in base
 *  2^52. */
typedef struct {
   /* A field element f represents the sum(i=0..4, f.n[i] << (i*52)) mod p,
    * where p is the field modulus, 2^256 - 2^32 - 977.
    *
    * The individual limbs f.n[i] can exceed 2^52; the field's magnitude roughly
    * corresponds to how much excess is allowed. The value
    * sum(i=0..4, f.n[i] << (i*52)) may exceed p, unless the field element is
    * normalized. */
    ulong n[5];
} secp256k1_fe;
typedef struct {
    secp256k1_fe x;
    secp256k1_fe y;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_ge;
typedef struct {
    secp256k1_fe x; /* actual X: x/z^2 */
    secp256k1_fe y; /* actual Y: y/z^3 */
    secp256k1_fe z;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_gej;
typedef struct { ulong n[4]; } secp256k1_fe_storage;
typedef struct {
    secp256k1_fe_storage x;
    secp256k1_fe_storage y;
} secp256k1_ge_storage;
static void secp256k1_fe_set_b32_mod(secp256k1_fe *r, const unsigned char *a) {
    r->n[0] = (ulong)a[31]
            | ((ulong)a[30] << 8)
            | ((ulong)a[29] << 16)
            | ((ulong)a[28] << 24)
            | ((ulong)a[27] << 32)
            | ((ulong)a[26] << 40)
            | ((ulong)(a[25] & 0xF)  << 48);
    r->n[1] = (ulong)((a[25] >> 4) & 0xF)
            | ((ulong)a[24] << 4)
            | ((ulong)a[23] << 12)
            | ((ulong)a[22] << 20)
            | ((ulong)a[21] << 28)
            | ((ulong)a[20] << 36)
            | ((ulong)a[19] << 44);
    r->n[2] = (ulong)a[18]
            | ((ulong)a[17] << 8)
            | ((ulong)a[16] << 16)
            | ((ulong)a[15] << 24)
            | ((ulong)a[14] << 32)
            | ((ulong)a[13] << 40)
            | ((ulong)(a[12] & 0xF) << 48);
    r->n[3] = (ulong)((a[12] >> 4) & 0xF)
            | ((ulong)a[11] << 4)
            | ((ulong)a[10] << 12)
            | ((ulong)a[9]  << 20)
            | ((ulong)a[8]  << 28)
            | ((ulong)a[7]  << 36)
            | ((ulong)a[6]  << 44);
    r->n[4] = (ulong)a[5]
            | ((ulong)a[4] << 8)
            | ((ulong)a[3] << 16)
            | ((ulong)a[2] << 24)
            | ((ulong)a[1] << 32)
            | ((ulong)a[0] << 40);
}
static void secp256k1_fe_from_storage(secp256k1_fe *r, const secp256k1_fe_storage *a) {
    r->n[0] = a->n[0] & 0xFFFFFFFFFFFFFUL;
    r->n[1] = a->n[0] >> 52 | ((a->n[1] << 12) & 0xFFFFFFFFFFFFFUL);
    r->n[2] = a->n[1] >> 40 | ((a->n[2] << 24) & 0xFFFFFFFFFFFFFUL);
    r->n[3] = a->n[2] >> 28 | ((a->n[3] << 36) & 0xFFFFFFFFFFFFFUL);
    r->n[4] = a->n[3] >> 16;
}
static void secp256k1_ge_set_xy(secp256k1_ge *r, const secp256k1_fe *x, const secp256k1_fe *y) {
    r->infinity = 0;
    r->x = *x;
    r->y = *y;
}
static void secp256k1_ge_from_storage(secp256k1_ge *r, const secp256k1_ge_storage *a) {
    secp256k1_fe_from_storage(&r->x, &a->x);
    secp256k1_fe_from_storage(&r->y, &a->y);
    r->infinity = 0;
}

/** Mathmatical functions for secp256k1_scalar_mul_512 and secp256k1_scalar_reduce_512. */
static void muladd_fast(ulong a, ulong b, ulong *c0, ulong *c1) {
	secp256k1_uint128 t;
	secp256k1_u128_mul(&t, a, b);
	*c0 += t.lo;           /* overflow is handled on the next line */
	t.hi += (*c0 < t.lo);  /* at most 0xFFFFFFFFFFFFFFFF */
    *c1 += t.hi;           /* never overflows by contract */
}
static void muladd(ulong a, ulong b, ulong *c0, ulong *c1, uint *c2) {
	secp256k1_uint128 t;
	secp256k1_u128_mul(&t, a, b);
	*c0 += t.lo;           // overflow is handled on the next line
	t.hi += (*c0 < t.lo);  // at most 0xFFFFFFFFFFFFFFFF
	*c1 += t.hi;           // overflow is handled on the next line
	*c2 += (*c1 < t.hi);   // never overflows by contract
}
static void muladd_ulong(ulong a, ulong b, ulong *c0, ulong *c1, ulong *c2) {
	secp256k1_uint128 t;
	secp256k1_u128_mul(&t, a, b);
	*c0 += t.lo;           // overflow is handled on the next line
	t.hi += (*c0 < t.lo);  // at most 0xFFFFFFFFFFFFFFFF
	*c1 += t.hi;           // overflow is handled on the next line
	*c2 += (*c1 < t.hi);   // never overflows by contract
}
static void extract_fast(ulong *n, ulong *c0, ulong *c1) {
	*n = *c0;
    *c0 = *c1;
    *c1 = 0;
}
static void extract(ulong *n, ulong *c0, ulong *c1, uint *c2) {
	*n = *c0;
    *c0 = *c1;
    *c1 = *c2;
    *c2 = 0;
}
static void extract_ulong(ulong *n, ulong *c0, ulong *c1, ulong *c2) {
	*n = *c0;
    *c0 = *c1;
    *c1 = *c2;
    *c2 = 0;
}
static void sumadd(ulong a, ulong *c0, ulong *c1, ulong *c2) { \
    uint over;
    *c0 += (a);            // overflow is handled on the next line
    over = (*c0 < (a));
    *c1 += over;           // overflow is handled on the next line
    *c2 += (*c1 < over);   // never overflows by contract
}
static void sumadd_fast(ulong a, ulong *c0, ulong *c1) {
    *c0 += (a);            // overflow is handled on the next line
    *c1 += (*c0 < (a));    // never overflows by contract (verified the next line)
}

/** A scalar modulo the group order of the secp256k1 curve. */
typedef struct { ulong d[4]; } secp256k1_scalar;
static int secp256k1_scalar_check_overflow(const secp256k1_scalar *a) {
    int yes = 0;
    int no = 0;
    no |= (a->d[3] < SECP256K1_N_3); /* No need for a > check. */
    no |= (a->d[2] < SECP256K1_N_2);
    yes |= (a->d[2] > SECP256K1_N_2) & ~no;
    no |= (a->d[1] < SECP256K1_N_1);
    yes |= (a->d[1] > SECP256K1_N_1) & ~no;
    yes |= (a->d[0] >= SECP256K1_N_0) & ~no;
    return yes;
}
static int secp256k1_scalar_is_high(const secp256k1_scalar *a) {
    int yes = 0;
    int no = 0;
    no |= (a->d[3] < SECP256K1_N_H_3);
    yes |= (a->d[3] > SECP256K1_N_H_3) & ~no;
    no |= (a->d[2] < SECP256K1_N_H_2) & ~yes; /* No need for a > check. */
    no |= (a->d[1] < SECP256K1_N_H_1) & ~yes;
    yes |= (a->d[1] > SECP256K1_N_H_1) & ~no;
    yes |= (a->d[0] > SECP256K1_N_H_0) & ~no;
    return yes;
}
static int secp256k1_scalar_is_zero(const secp256k1_scalar *a) {
    return (a->d[0] | a->d[1] | a->d[2] | a->d[3]) == 0;
}
// NEEDS TESTING - Redo this garbage
static int secp256k1_scalar_reduce(secp256k1_scalar *r, unsigned int overflow) {
    secp256k1_uint128 t;

    //secp256k1_u128_from_u64(&t, r->d[0]);
	t.lo = r->d[0];
    
	//secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_0);
	secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_0);
 
	//r->d[0] = secp256k1_u128_to_u64(&t);
	r->d[0] = t.lo;
	
	//secp256k1_u128_rshift(&t, 64);
    t.lo = t.hi;
	t.hi = 0;
	
	//secp256k1_u128_accum_u64(&t, r->d[1]);
	secp256k1_u128_accum_u64(&t, r->d[1]);

    //secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_1);
	secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_1);
    
	//r->d[1] = secp256k1_u128_to_u64(&t);
	r->d[1] = t.lo;

	// secp256k1_u128_rshift(&t, 64);
	t.lo = t.hi;
	t.hi = 0;

    //secp256k1_u128_accum_u64(&t, r->d[2]);
	secp256k1_u128_accum_u64(&t, r->d[2]);

    //secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_2);
	secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_2);

    //r->d[2] = secp256k1_u128_to_u64(&t);
	r->d[2] = t.lo;

	//secp256k1_u128_rshift(&t, 64);
	t.lo = t.hi;
	t.hi = 0;
    
	//secp256k1_u128_accum_u64(&t, r->d[3]);
	secp256k1_u128_accum_u64(&t, r->d[3]);

    //r->d[3] = secp256k1_u128_to_u64(&t);
    r->d[3] = t.lo;

	return overflow;
}
static void secp256k1_scalar_set_b32(secp256k1_scalar *r, const unsigned char *b32, int *overflow) {
    int over;
    r->d[0] = (ulong)b32[31] | (ulong)b32[30] << 8 | (ulong)b32[29] << 16 | (ulong)b32[28] << 24 | (ulong)b32[27] << 32 | (ulong)b32[26] << 40 | (ulong)b32[25] << 48 | (ulong)b32[24] << 56;
    r->d[1] = (ulong)b32[23] | (ulong)b32[22] << 8 | (ulong)b32[21] << 16 | (ulong)b32[20] << 24 | (ulong)b32[19] << 32 | (ulong)b32[18] << 40 | (ulong)b32[17] << 48 | (ulong)b32[16] << 56;
    r->d[2] = (ulong)b32[15] | (ulong)b32[14] << 8 | (ulong)b32[13] << 16 | (ulong)b32[12] << 24 | (ulong)b32[11] << 32 | (ulong)b32[10] << 40 | (ulong)b32[9] << 48 | (ulong)b32[8] << 56;
    r->d[3] = (ulong)b32[7] | (ulong)b32[6] << 8 | (ulong)b32[5] << 16 | (ulong)b32[4] << 24 | (ulong)b32[3] << 32 | (ulong)b32[2] << 40 | (ulong)b32[1] << 48 | (ulong)b32[0] << 56;
    over = secp256k1_scalar_reduce(r, secp256k1_scalar_check_overflow(r));
    if (overflow) {
        *overflow = over;
    }
}
static void secp256k1_scalar_from_signed62(secp256k1_scalar *r, const secp256k1_modinv64_signed62 *a) {
    const ulong a0 = a->v[0], a1 = a->v[1], a2 = a->v[2], a3 = a->v[3], a4 = a->v[4];
    r->d[0] = a0      | a1 << 62;
    r->d[1] = a1 >> 2 | a2 << 60;
    r->d[2] = a2 >> 4 | a3 << 58;
    r->d[3] = a3 >> 6 | a4 << 56;
}
static void secp256k1_scalar_to_signed62(secp256k1_modinv64_signed62 *r, const secp256k1_scalar *a) {
    const ulong M62 = ULONG_MAX >> 2;
    const ulong a0 = a->d[0], a1 = a->d[1], a2 = a->d[2], a3 = a->d[3];
    r->v[0] =  a0                   & M62;
    r->v[1] = (a0 >> 62 | a1 <<  2) & M62;
    r->v[2] = (a1 >> 60 | a2 <<  4) & M62;
    r->v[3] = (a2 >> 58 | a3 <<  6) & M62;
    r->v[4] =  a3 >> 56;
}
static void secp256k1_scalar_inverse_var(secp256k1_scalar *r, const secp256k1_scalar *x) {
    secp256k1_modinv64_signed62 s;

    secp256k1_scalar_to_signed62(&s, x);
    secp256k1_modinv64_var(&s, &secp256k1_const_modinfo_scalar);
    secp256k1_scalar_from_signed62(r, &s);
}
static void secp256k1_scalar_mul_512(ulong l[8], const secp256k1_scalar *a, const secp256k1_scalar *b) {
    /* 160 bit accumulator. */
    ulong c0 = 0, c1 = 0;
    uint c2 = 0;

    /* l[0..7] = a[0..3] * b[0..3]. */
    muladd_fast(a->d[0], b->d[0], &c0, &c1);
    extract_fast(&l[0], &c0, &c1);
    muladd(a->d[0], b->d[1], &c0, &c1, &c2);
    muladd(a->d[1], b->d[0], &c0, &c1, &c2);
    extract(&l[1], &c0, &c1, &c2);
    muladd(a->d[0], b->d[2], &c0, &c1, &c2);
    muladd(a->d[1], b->d[1], &c0, &c1, &c2);
    muladd(a->d[2], b->d[0], &c0, &c1, &c2);
    extract(&l[2], &c0, &c1, &c2);
    muladd(a->d[0], b->d[3], &c0, &c1, &c2);
    muladd(a->d[1], b->d[2], &c0, &c1, &c2);
    muladd(a->d[2], b->d[1], &c0, &c1, &c2);
    muladd(a->d[3], b->d[0], &c0, &c1, &c2);
    extract(&l[3], &c0, &c1, &c2);
    muladd(a->d[1], b->d[3], &c0, &c1, &c2);
    muladd(a->d[2], b->d[2], &c0, &c1, &c2);
    muladd(a->d[3], b->d[1], &c0, &c1, &c2);
    extract(&l[4], &c0, &c1, &c2);
    muladd(a->d[2], b->d[3], &c0, &c1, &c2);
    muladd(a->d[3], b->d[2], &c0, &c1, &c2);
    extract(&l[5], &c0, &c1, &c2);
    muladd_fast(a->d[3], b->d[3], &c0, &c1);
    extract_fast(&l[6], &c0, &c1);
    l[7] = c0;
}
static void secp256k1_scalar_reduce_512(secp256k1_scalar *r, const ulong *l) {
    secp256k1_uint128 c128;

    ulong c, c0, c1, c2;
    ulong n0 = l[4], n1 = l[5], n2 = l[6], n3 = l[7];
    ulong m0, m1, m2, m3, m4, m5; uint m6;
    ulong p0, p1, p2, p3; uint p4;

    /* Reduce 512 bits into 385. */
    /* m[0..6] = l[0..3] + n[0..3] * SECP256K1_N_C. */
    c0 = l[0]; c1 = 0; c2 = 0;
    muladd_fast(n0, SECP256K1_N_C_0, &c0, &c1);
    extract_fast(&m0, &c0, &c1);
    sumadd_fast(l[1], &c0, &c1);
	muladd_ulong(n1, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(n0, SECP256K1_N_C_1, &c0, &c1, &c2);
    extract_ulong(&m1, &c0, &c1, &c2);
    sumadd(l[2], &c0, &c1, &c2);
	muladd_ulong(n2, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(n1, SECP256K1_N_C_1, &c0, &c1, &c2);
    sumadd(n0, &c0, &c1, &c2);
    extract_ulong(&m2, &c0, &c1, &c2);
    sumadd(l[3], &c0, &c1, &c2);
	muladd_ulong(n3, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(n2, SECP256K1_N_C_1, &c0, &c1, &c2);
    sumadd(n1, &c0, &c1, &c2);
    extract_ulong(&m3, &c0, &c1, &c2);
    muladd_ulong(n3, SECP256K1_N_C_1, &c0, &c1, &c2);
    sumadd(n2, &c0, &c1, &c2);
    extract_ulong(&m4, &c0, &c1, &c2);
    sumadd_fast(n3, &c0, &c1);
    extract_fast(&m5, &c0, &c1);
    m6 = c0;

    /* Reduce 385 bits into 258. */
    /* p[0..4] = m[0..3] + m[4..6] * SECP256K1_N_C. */
    c0 = m0; c1 = 0; c2 = 0;
    muladd_fast(m4, SECP256K1_N_C_0, &c0, &c1);
    extract_fast(&p0, &c0, &c1);
    sumadd_fast(m1, &c0, &c1);
    muladd_ulong(m5, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(m4, SECP256K1_N_C_1, &c0, &c1, &c2);
    extract_ulong(&p1, &c0, &c1, &c2);
    sumadd(m2, &c0, &c1, &c2);
    muladd_ulong(m6, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(m5, SECP256K1_N_C_1, &c0, &c1, &c2);
	sumadd(m4, &c0, &c1, &c2);
    extract_ulong(&p2, &c0, &c1, &c2);
    sumadd_fast(m3, &c0, &c1);
    muladd_fast(m6, SECP256K1_N_C_1, &c0, &c1);
    sumadd_fast(m5, &c0, &c1);
    extract_fast(&p3, &c0, &c1);
    p4 = c0 + m6;

    /* Reduce 258 bits into 256. */
    /* r[0..3] = p[0..3] + p[4] * SECP256K1_N_C. */
    secp256k1_u128_from_u64(&c128, p0);
    secp256k1_u128_accum_mul(&c128, SECP256K1_N_C_0, p4);
    r->d[0] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p1);
    secp256k1_u128_accum_mul(&c128, SECP256K1_N_C_1, p4);
    r->d[1] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p2);
    secp256k1_u128_accum_u64(&c128, p4);
    r->d[2] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p3);
    r->d[3] = secp256k1_u128_to_u64(&c128);
    c = secp256k1_u128_hi_u64(&c128);

    /* Final reduction of r. */
    secp256k1_scalar_reduce(r, c + secp256k1_scalar_check_overflow(r));
}
static void secp256k1_scalar_mul(secp256k1_scalar *r, const secp256k1_scalar *a, const secp256k1_scalar *b) {
    ulong l[8];
    secp256k1_scalar_mul_512(l, a, b);
    secp256k1_scalar_reduce_512(r, l);
}

typedef struct { unsigned char data[64]; } secp256k1_pubkey;
typedef struct { unsigned char data[64]; } secp256k1_ecdsa_signature;
static void secp256k1_ecdsa_signature_load(secp256k1_scalar* r, secp256k1_scalar* s, const secp256k1_ecdsa_signature* sig) {
    if (sizeof(secp256k1_scalar) == 32) {
        /* When the secp256k1_scalar type is exactly 32 byte, use its
         * representation inside secp256k1_ecdsa_signature, as conversion is very fast.
         * Note that secp256k1_ecdsa_signature_save must use the same representation. */
        memcpy(r, &sig->data[0], 32);
        memcpy(s, &sig->data[32], 32);
    } else {
        secp256k1_scalar_set_b32(r, &sig->data[0], 0);
        secp256k1_scalar_set_b32(s, &sig->data[32], 0);
    }
}
static int secp256k1_pubkey_load(secp256k1_ge* ge, const secp256k1_pubkey* pubkey) {
    if (sizeof(secp256k1_ge_storage) == 64) {
        /* When the secp256k1_ge_storage type is exactly 64 byte, use its
         * representation inside secp256k1_pubkey, as conversion is very fast.
         * Note that secp256k1_pubkey_save must use the same representation. */
        secp256k1_ge_storage s;

		// TODO: Implement custom memcpy
        memcpy(&s, &pubkey->data[0], sizeof(s));
        secp256k1_ge_from_storage(ge, &s);
    } else {
        /* Otherwise, fall back to 32-byte big endian for X and Y. */
        secp256k1_fe x, y;
        secp256k1_fe_set_b32_mod(&x, pubkey->data);
        secp256k1_fe_set_b32_mod(&y, pubkey->data + 32);
        secp256k1_ge_set_xy(ge, &x, &y);
    }
    return 1;
}
static int secp256k1_ecdsa_sig_verify(const secp256k1_scalar *sigr, const secp256k1_scalar *sigs, const secp256k1_ge *pubkey, const secp256k1_scalar *message) {
    uchar c[32];
    secp256k1_scalar sn, u1, u2;
    secp256k1_fe xr;
    secp256k1_gej pubkeyj;
    secp256k1_gej pr;

    if (secp256k1_scalar_is_zero(sigr) || secp256k1_scalar_is_zero(sigs)) {
        return 0;
    }

    secp256k1_scalar_inverse_var(&sn, sigs);
    secp256k1_scalar_mul(&u1, &sn, message);
    secp256k1_scalar_mul(&u2, &sn, sigr);
    secp256k1_gej_set_ge(&pubkeyj, pubkey);
    secp256k1_ecmult(&pr, &pubkeyj, &u2, &u1);
    if (secp256k1_gej_is_infinity(&pr)) {
        return 0;
    }

    secp256k1_scalar_get_b32(c, sigr);
    /* we can ignore the fe_set_b32_limit return value, because we know the input is in range */
    (void)secp256k1_fe_set_b32_limit(&xr, c);

    /** We now have the recomputed R point in pr, and its claimed x coordinate (modulo n)
     *  in xr. Naively, we would extract the x coordinate from pr (requiring a inversion modulo p),
     *  compute the remainder modulo n, and compare it to xr. However:
     *
     *        xr == X(pr) mod n
     *    <=> exists h. (xr + h * n < p && xr + h * n == X(pr))
     *    [Since 2 * n > p, h can only be 0 or 1]
     *    <=> (xr == X(pr)) || (xr + n < p && xr + n == X(pr))
     *    [In Jacobian coordinates, X(pr) is pr.x / pr.z^2 mod p]
     *    <=> (xr == pr.x / pr.z^2 mod p) || (xr + n < p && xr + n == pr.x / pr.z^2 mod p)
     *    [Multiplying both sides of the equations by pr.z^2 mod p]
     *    <=> (xr * pr.z^2 mod p == pr.x) || (xr + n < p && (xr + n) * pr.z^2 mod p == pr.x)
     *
     *  Thus, we can avoid the inversion, but we have to check both cases separately.
     *  secp256k1_gej_eq_x implements the (xr * pr.z^2 mod p == pr.x) test.
     */
    if (secp256k1_gej_eq_x_var(&xr, &pr)) {
        /* xr * pr.z^2 mod p == pr.x, so the signature is valid. */
        return 1;
    }
    if (secp256k1_fe_cmp_var(&xr, &secp256k1_ecdsa_const_p_minus_order) >= 0) {
        /* xr + n >= p, so we can skip testing the second case. */
        return 0;
    }
    secp256k1_fe_add(&xr, &secp256k1_ecdsa_const_order_as_fe);
    if (secp256k1_gej_eq_x_var(&xr, &pr)) {
        /* (xr + n) * pr.z^2 mod p == pr.x, so the signature is valid. */
        return 1;
    }
    return 0;
}

static int secp256k1_ecdsa_verify(const secp256k1_ecdsa_signature *sig, const unsigned char *msghash32, const secp256k1_pubkey *pubkey) {
    secp256k1_ge q;
    secp256k1_scalar r, s;
    secp256k1_scalar m;

    secp256k1_scalar_set_b32(&m, msghash32, 0);
    secp256k1_ecdsa_signature_load(&r, &s, sig);
    return (!secp256k1_scalar_is_high(&s) &&
            secp256k1_pubkey_load(&q, pubkey) &&
            secp256k1_ecdsa_sig_verify(&r, &s, &q, &m));
}