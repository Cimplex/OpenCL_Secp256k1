// Constants

/* Limbs of half the secp256k1 order. */
#define SECP256K1_N_H_0 (0xDFE92F46681B20A0UL)
#define SECP256K1_N_H_1 (0x5D576E7357A4501DUL)
#define SECP256K1_N_H_2 (0xFFFFFFFFFFFFFFFFUL)
#define SECP256K1_N_H_3 (0x7FFFFFFFFFFFFFFFUL)

/* Limbs of the secp256k1 order. */
#define SECP256K1_N_0 (0xBFD25E8CD0364141UL)
#define SECP256K1_N_1 (0xBAAEDCE6AF48A03BUL)
#define SECP256K1_N_2 (0xFFFFFFFFFFFFFFFEUL)
#define SECP256K1_N_3 (0xFFFFFFFFFFFFFFFFUL)

/* Limbs of 2^256 minus the secp256k1 order. */
#define SECP256K1_N_C_0 (~SECP256K1_N_0 + 1)
#define SECP256K1_N_C_1 (~SECP256K1_N_1)
#define SECP256K1_N_C_2 (1)

// OpenCL-Type -> C-Type
typedef struct {
    ulong hi; // Higher 64 bits
    ulong lo; // Lower 64 bits
} secp256k1_uint128;

typedef struct {
    ulong d[4];
} secp256k1_scalar;

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

	// No verify

} secp256k1_fe;

typedef struct {
    ulong n[4];
} secp256k1_fe_storage;

typedef struct {
    secp256k1_fe x;
    secp256k1_fe y;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_ge;

typedef struct {
    secp256k1_fe_storage x;
    secp256k1_fe_storage y;
} secp256k1_ge_storage;

typedef struct {
    secp256k1_fe x; /* actual X: x/z^2 */
    secp256k1_fe y; /* actual Y: y/z^3 */
    secp256k1_fe z;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_gej;

typedef struct {
    /* Whether the context has been built. */
    int built;

    /* Blinding values used when computing (n-b)G + bG. */
    secp256k1_scalar blind; /* -b */
    secp256k1_gej initial;  /* bG */
} secp256k1_ecmult_gen_context;

struct secp256k1_context_struct {
    secp256k1_ecmult_gen_context ecmult_gen_ctx;
    
	// TODO: Add some way of error checking? not sure what these do yet
	//secp256k1_callback illegal_callback;
    //secp256k1_callback error_callback;
    int declassify;
};

typedef struct secp256k1_context_struct secp256k1_context;

typedef struct {
    uchar data[64];
} secp256k1_ecdsa_signature;

typedef struct {
    uchar data[64];
} secp256k1_pubkey;

static void memcpy_opencl(uchar* src, uchar* dest, size_t numElements)
{
    for (size_t i = 0; i < numElements; ++i)
    {
        dest[i] = src[i];
    }
}

static void secp256k1_u128_from_u64(secp256k1_uint128 *r, ulong a) {
   r->lo = a;
}

static void secp256k1_u128_accum_u64(secp256k1_uint128 *r, ulong a) {
	ulong sum_lo = r->lo + a;
    r->hi += (sum_lo < r->lo) ? 1 : 0;  // Check for overflow
    r->lo = sum_lo;
}

static ulong secp256k1_u128_to_u64(const secp256k1_uint128 *a) {
   return a->lo;
}

static void secp256k1_u128_rshift_64(secp256k1_uint128 *r) {
   r->lo = r->hi;
   r->hi = 0;
}

static secp256k1_fe_from_storage(secp256k1_fe *r, const secp256k1_fe_storage *a) {
    r->n[0] = a->n[0] & 0xFFFFFFFFFFFFFUL;
    r->n[1] = a->n[0] >> 52 | ((a->n[1] << 12) & 0xFFFFFFFFFFFFFUL);
    r->n[2] = a->n[1] >> 40 | ((a->n[2] << 24) & 0xFFFFFFFFFFFFFUL);
    r->n[3] = a->n[2] >> 28 | ((a->n[3] << 36) & 0xFFFFFFFFFFFFFUL);
    r->n[4] = a->n[3] >> 16;
}

static void secp256k1_ge_from_storage(secp256k1_ge *r, const secp256k1_ge_storage *a) {
    secp256k1_fe_from_storage(&r->x, &a->x);
    secp256k1_fe_from_storage(&r->y, &a->y);
    r->infinity = 0;
    secp256k1_ge_verify(r);
}

static int secp256k1_scalar_reduce(secp256k1_scalar *r, unsigned int overflow) {
    secp256k1_uint128 t;

    secp256k1_u128_from_u64(&t, r->d[0]);
    secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_0);

    r->d[0] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift_64(&t);

	secp256k1_u128_accum_u64(&t, r->d[1]);
    secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_1);

	r->d[1] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift_64(&t);

	secp256k1_u128_accum_u64(&t, r->d[2]);
    secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_2);

	r->d[2] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift_64(&t);

	secp256k1_u128_accum_u64(&t, r->d[3]);

	r->d[3] = secp256k1_u128_to_u64(&t);

	return overflow;
}

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

static void secp256k1_scalar_set_b32(secp256k1_scalar *r, const unsigned char *b32, int *overflow) {
    int over;
    r->d[0] = (ulong)b32[31] | (ulong)b32[30] << 8 | (ulong)b32[29] << 16 | (ulong)b32[28] << 24 | (ulong)b32[27] << 32 | (ulong)b32[26] << 40 | (ulong)b32[25] << 48 | (ulong)b32[24] << 56;
    r->d[1] = (ulong)b32[23] | (ulong)b32[22] << 8 | (ulong)b32[21] << 16 | (ulong)b32[20] << 24 | (ulong)b32[19] << 32 | (ulong)b32[18] << 40 | (ulong)b32[17] << 48 | (ulong)b32[16] << 56;
    r->d[2] = (ulong)b32[15] | (ulong)b32[14] << 8 | (ulong)b32[13] << 16 | (ulong)b32[12] << 24 | (ulong)b32[11] << 32 | (ulong)b32[10] << 40 | (ulong)b32[9] << 48  | (ulong)b32[8] << 56;
    r->d[3] = (ulong)b32[7]  | (ulong)b32[6] << 8  | (ulong)b32[5] << 16  | (ulong)b32[4] << 24  | (ulong)b32[3] << 32  | (ulong)b32[2] << 40  | (ulong)b32[1] << 48  | (ulong)b32[0] << 56;
    over = secp256k1_scalar_reduce(r, secp256k1_scalar_check_overflow(r));
    if (overflow) {
        *overflow = over;
    }
}

// TODO: Removed const from 'sig'... check to see if this is ok
static void secp256k1_ecdsa_signature_load(const secp256k1_context* ctx, secp256k1_scalar* r, secp256k1_scalar* s, secp256k1_ecdsa_signature* sig) {
    (void)ctx;
    if (sizeof(secp256k1_scalar) == 32) {
        /* When the secp256k1_scalar type is exactly 32 byte, use its
         * representation inside secp256k1_ecdsa_signature, as conversion is very fast.
         * Note that secp256k1_ecdsa_signature_save must use the same representation. */
        memcpy_opencl((uchar*)r, &sig->data[0], 32);
        memcpy_opencl((uchar*)s, &sig->data[32], 32);
    } else {
        secp256k1_scalar_set_b32(r, &sig->data[0], 0);
        secp256k1_scalar_set_b32(s, &sig->data[32], 0);
    }
}

static int secp256k1_pubkey_load(const secp256k1_context* ctx, secp256k1_ge* ge, const secp256k1_pubkey* pubkey) {
    if (sizeof(secp256k1_ge_storage) == 64) {
        /* When the secp256k1_ge_storage type is exactly 64 byte, use its
         * representation inside secp256k1_pubkey, as conversion is very fast.
         * Note that secp256k1_pubkey_save must use the same representation. */
        secp256k1_ge_storage s;
        memcpy_opencl(&s, &pubkey->data[0], sizeof(s));
        secp256k1_ge_from_storage(ge, &s);
    } else {
        /* Otherwise, fall back to 32-byte big endian for X and Y. */
        secp256k1_fe x, y;
        secp256k1_fe_set_b32_mod(&x, pubkey->data);
        secp256k1_fe_set_b32_mod(&y, pubkey->data + 32);
        secp256k1_ge_set_xy(ge, &x, &y);
    }
    ARG_CHECK(!secp256k1_fe_is_zero(&ge->x));
    return 1;
}

int secp256k1_ecdsa_verify(const secp256k1_context* ctx, secp256k1_ecdsa_signature *sig, const unsigned char *msghash32, const secp256k1_pubkey *pubkey);

// TODO: Removed const from 'sig'... check to see if this is ok
int secp256k1_ecdsa_verify(const secp256k1_context* ctx, secp256k1_ecdsa_signature *sig, const unsigned char *msghash32, const secp256k1_pubkey *pubkey) {
    secp256k1_ge q;
    secp256k1_scalar r, s;
    secp256k1_scalar m;

    secp256k1_scalar_set_b32(&m, msghash32, 0);

    secp256k1_ecdsa_signature_load(ctx, &r, &s, sig);
    return (!secp256k1_scalar_is_high(&s) &&
            secp256k1_pubkey_load(ctx, &q, pubkey) &&
            secp256k1_ecdsa_sig_verify(&r, &s, &q, &m));
}


__kernel void secp256k1_verify( __global uchar*   input,
	                            __global uchar*   output) {
	int x = get_global_id(0);       // x
	int y = get_global_id(1);       // y
	int z = get_global_id(2);       // z
	int w = get_global_size(0);     // x.length (width)
	int h = get_global_size(1);     // y.length (height)

	secp256k1_scalar s;

}