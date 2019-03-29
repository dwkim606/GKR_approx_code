//============================================================================
// Name        : GKR protocol over R
// Author      : Dongwoo Kim
// Version     : 1.0
// Copyright   :
// Description : Micro benchmark for Matmult followed by rounding
//============================================================================

#include <chrono>
#include <iostream>
#include <fstream>
#include <stdint.h>
#include <math.h>
#include <random>
#include <ctime>
#include <pthread.h>
#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/BasicThreadPool.h>

using namespace std;
using namespace NTL;

// Parameter restrictions for correctness of our algorithm//
// PRIME^E < 2^127 for fast arithmetic
// PRIME^{E+1} < 2^128
// E < 2*P  for LDpoly calculation
// ConstMult with C s.t. C*PRIME^E < 2^127 is followed by myModMult is allowed without myMod (We use C = 3 for X^4-3 = 0)

#define PRIME 271 // 17 	// PRIME^E < 2^123
#define E 14
#define PE ZZ(power(ZZ(PRIME), E))
#define digitRep 10
#define DIM 2
#define ETA 16

#define PRIME_TH 2305843009213693951		// for Thaler
#define MASK 4294967295					// for Thaler

typedef uint64_t uint64;
typedef __uint128_t uint128;
typedef int (*fptr)(int, int);

//circuit data structure
typedef struct circ{
	uint128** gates; //two-d array of gates
	fptr* in1;
	fptr* in2;
	fptr* types;
	int num_levels;
	int* sublv_length;				// length of each sub level
	int* log_sublv_length;
	int* sublv_num;					// number of sub levels (sub circuits)
	int* log_sublv_num;
	int round_level_st;
	int* testtype;
} circ;

typedef struct rElt{
	uint128 c[DIM]; // [0]: constant , [1]: deg 1 coeff ...
} rElt;

static uint128* PRIMES = new uint128[E+1];	// Keeps PRIME^i 				for each i in {0, 1, ..., E}
static uint128* _P = new uint128[E+1];		// Keeps -PRIME^(-i) mod 2^128 	for each i in {0, 1, ..., E}
static uint128* R2 = new uint128[E+1];		// Keeps 2^256 mod PRIME^(i) 	for each i in {0, 1, ..., E}
static uint128 MASK64;						// 2^64 - 1
static uint128 MASK127;						// 2^127 - 1
static uint128 NUMER;						// smallest integer larger than 2^128 / PRIME	for fast division by PRIME
static uint128** CST = new uint128*[PRIME];	// Keeps Motgomery form of 1,2,...,PRIME-1  mod PRIME^i 	for each i in {0, 1, ..., E}
static rElt** CSTR = new rElt*[PRIME];	// Keeps Motgomery form of 0,1,2,...,PRIME-1, t, t+1, ... (total# E*PRIME) mod PRIME^i 	for each i in {0, 1, ..., E}
static uint128** invCST = new uint128*[PRIME];	// Keeps Motgomery form of 1,2,...,PRIME-1  mod PRIME^i 	for each i in {0, 1, ..., E}
//static rElt** lagW = new rElt*[E*PRIME];		// Keeps Motgomery form of w_0, w_1, ..., w_ep-1 for Lagrange interpolation  mod PRIME^i 	for each i in {0, 1, ..., E}
static long LV;								// Curruent level
static long* LOG_ep = new long[E+1];				// log of e*PRIME for each e in {0, 1, ... lev}
static long* LOG_sqr_ep = new long[E+1];			// log of sqrt(e*PRIME) for each e in {0, 1, ... lev}
static long* LOG_rem = new long[E+1];			// log of e*PRIME for each e in {0, 1, ... lev}
static rElt ONE;
static rElt ZERO;
static int GAMMA;

random_device rd;
mt19937_64 gen(rd());
uniform_int_distribution<unsigned long long> unif;


/*******************/
/* basic functions  *
/*******************/

// Hensel Quadratic Modular inverse for 2^e
uint128 invModPo2(uint128 x, long e){
	if(x&1){
		uint128 u = 1;
		uint128 tmp;

		for (long i = 2; i < e;  i <<= 1){
			tmp = u * u;
			tmp = tmp * x;
			tmp = (tmp << (128-i)) >> (128-i);
			u <<= 1;
			u -= tmp;
		}

		tmp = u * u;
		tmp = tmp * x;
		u <<= 1;
		u -= tmp;

		return u;
	}
	else{
		cout << "No inverse!"<< endl;
		return 0;
	}
}

// x^pow for uint128
uint128 myPow(uint128 x, uint128 pow){
	uint128 i = 1;
	for (long j = 0; j < pow; ++j)
		i *= x;
	return i;
}

// modulo PRIME^E given x in [0, 2^128), only needs for parameter setting, so it does not need to be efficient
uint128 myModPE(uint128 x){
//	uint128 res = (x >> 127) * CONST + (x & MASK127);  // makes that res < 2 * PRIME^E
//	return (res -  (res >= PRIMES[E]) * PRIMES[E]);
	return (x%PRIMES[E]);
}


/**************************************************************/
/* Mod PRIME^LV arithmetic functions with Montgomery reduction*
/**************************************************************/

// modulo PRIME^lev given x in [0, 2*PRIME^lev) only for addition or doubling!
inline uint128 myMod(uint128 x, long lev = LV){
	return (x - (x >= PRIMES[lev]) * PRIMES[lev]);
}

// REDC algo for Montgomery reduction with r = 2^128.
// for input T = T0 + T1 * r in [0, r*PRIME^lev), returns T * r^(-1) mod (PRIME^lev)
inline uint128 REDC(uint128 T0, uint128 T1, long lev = LV){
	uint128 m = T0 * _P[lev];

	uint128 high_m = m >> 64;
	uint128 low_m = m & MASK64;
	uint128 high_n = PRIMES[lev] >> 64;
	uint128 low_n = PRIMES[lev] & MASK64;

	uint128 mN = low_m * high_n;
	uint128 Mn = low_n * high_m;

	uint128 high = high_m*high_n + (mN >> 64) + (Mn >> 64);
	uint128 low1 = low_m * low_n;
	uint128 low2 = (mN & MASK64) << 64;
	uint128 low3 = (Mn & MASK64) << 64;

	uint128 carry = 0;
	carry += ((low1 + low2) < low2);
	carry += ((low1 + low2 + low3) < low3);

	uint128 t = T1 + high + carry + (T0 != 0);

	return (t - (t >= PRIMES[lev]) * PRIMES[lev]);
}

// convert x (mod PRIME^lev) to rx (mod PRIME^lev) for Montgomery
uint128 conv_to_mon(uint128 x, long lev = LV){
	uint128 high_x = x >> 64;
	uint128 low_x = x & MASK64;
	uint128 high_R2 = R2[lev] >> 64;
	uint128 low_R2 = R2[lev] & MASK64;

	uint128 high = high_x * high_R2;
	uint128 mid = high_x * low_R2 + low_x * high_R2;		// possible since x, R2 both less than 2^127
	uint128 low = low_x * low_R2;

	high += (mid >> 64);
	low += ((mid & MASK64) << 64);
	high += (((mid & MASK64) << 64) > low);		// manage carry

	return REDC(low, high, lev);
}

// convert montgomery from rx (mod PRIME^lev) to x (mod PRIME^lev)
uint128 conv_from_mon(uint128 xm, long lev = LV){
	return REDC(xm, 0, lev);
}

// xm, ym is assumed to be in [0, PRIME^lev) and is in Mongomery form
inline uint128 myModMult(uint128 xm, uint128 ym, long lev = LV){
	uint128 high_xm = xm >> 64;
	uint128 low_xm = xm & MASK64;
	uint128 high_ym = ym >> 64;
	uint128 low_ym = ym & MASK64;

	uint128 high = high_xm * high_ym;
	uint128 mid = high_xm * low_ym + low_xm * high_ym;		// possible since xm, ym both less than 2^127
	uint128 low = low_xm * low_ym;

	high += (mid >> 64);
	low += ((mid & MASK64) << 64);
	high += (((mid & MASK64) << 64) > low);		// manage carry

	return REDC(low, high, lev);
}

// Extended Euclidean Algorithm mod PRIME for inverse mod PRIME^lev
// u1 * x + u2 * v3 = gcd(x, v3) = u3	where v3 = PRIME
void extEuclideanAlg_p(int x, int* u1, int* u2, int* u3){
	*u1 = 1;
	*u2 = 0;
	*u3 = x;
	int v1 = 0;
	int v2 = 1;
	int v3 = PRIME;
	int q;
	int t1, t2, t3;

	do{
		q = *u3 / v3;
		t1 = (*u1) - q*v1;
	    t2 = (*u2) - q*v2;
	    t3 = (*u3) - q*v3;
	    (*u1) = v1;
	    (*u2) = v2;
	    (*u3) = v3;
	    v1 = t1;
	    v2 = t2;
	    v3 = t3;
	}while (v3!=0);
	*u1 = (((*u1)%PRIME) + PRIME)%PRIME;
}

// Hensel Quadratic Modular inverse mod PRIME^lev.
// input&output is in Montgomery form and in [0, PRIME^lev).
uint128 inv(uint128 xm, long lev = LV){
	int u1, u2, u3;
	uint128 tmp;
	uint128 a = conv_to_mon(xm, lev);
	extEuclideanAlg_p(xm%PRIME, &u1, &u2, &u3);
	if(u3!=1){
		cout << "No inverse!"<< u1 <<", "<< u2 <<", "<< u3 << endl;
		return 0;
	}
	uint128 u = u1;

	u = conv_to_mon(u, lev);
	for (uint128 i = 2; i < lev; i <<= 1){
		tmp = myModMult(u, u, lev);
		tmp = myModMult(tmp, a, lev);
		u = myMod(2*u, lev);
		u = myMod(u + PRIMES[lev] - tmp, lev);
	}
	tmp = myModMult(u, u, lev);
	tmp = myModMult(tmp, a, lev);
	u = myMod(2*u, lev);
	u = myMod(u + PRIMES[lev] - tmp, lev);

	return myModMult(u, R2[lev], lev);
}


// given xp + r in [0, PRIMES[E] < 2^127), returns x where r in [0, p). NEED PRIMES^[E+1] < 2^128!
// use the approximation of 1/p by NUMER/2^128
uint128 div_p(uint128 xp){
	uint128 high_xp = xp >> 64;
	uint128 low_xp = xp & MASK64;
	uint128 high_N = NUMER >> 64;
	uint128 low_N = NUMER & MASK64;

	uint128 high = high_xp * high_N;
	uint128 mid = high_xp * low_N + low_xp * high_N;		// possible since xp, NUMER both less than 2^127
	uint128 low = low_xp * low_N;

	high += (mid >> 64);
	low += ((mid & MASK64) << 64);
	high += (((mid & MASK64) << 64) > low);		// manage carry

	return high;
}

// Does it need?
// compute x^pow (mod PRIME^E) // input&output are in Montgomery form
uint128 myModPow(uint128 xm, uint128 pow){
	uint128 res;
	if (pow == 0) return 1;
	if (pow == 1) return xm;
	if ((pow&1) == 0){
		res = myModPow(xm, (pow >> 1));
		return myModMult(res, res, E);
	}
	else
		return myModMult(myModPow(xm, pow-1), xm, E);
}

// evaluate polynomial at given input vec, coeff[1] <-> 1st degree
// input&output are in Montgomery form
uint128 evalPolyVec(uint128* coeff, uint128* input, long st, long deg, long lev = LV){
	uint128 res = 0;
	for (long i = 0; i < deg; ++i)
		res = myMod(res + myModMult(coeff[i], input[st+i], lev), lev);

	return res;
}


// evaluate polynomial at given input vec, coeff[0] <-> 1st degree
// input&output are in Montgomery form
uint128 evalPolyVec_old(uint128* coeff, uint128* input, long st, long deg, long lev = LV){
	uint128 res = 0;
	for (long i = 0; i < deg; ++i)
		res = myMod(res + myModMult(coeff[i], input[st+i], lev), lev);

	return res;
}


// simple rounding without LDpoly
// input&output are in Montgomery form
uint128 simRounding(uint128 input, long lev = LV){
	uint128 tmp = conv_from_mon(input, lev);
	uint128 a = tmp%PRIME;
	if (a > (PRIME-1)/2)
		return conv_to_mon(tmp + PRIME - a, lev);
	else
		return conv_to_mon(tmp - a, lev);
}


// simple rounding without LDpoly
// input&output are in Montgomery form
uint128 simRounding_op(uint128 input, long lev = LV){
	uint128 res = conv_from_mon(input, lev);
	res = res - div_p(res)*PRIME;
	if (res > (PRIME-1)/2)
		return conv_to_mon(input + PRIME - res, lev);
	else
		return conv_to_mon(input - res, lev);
}


// 128 rand generator  (less than 10 clock), sim to rand()
uint128 rand_128(uniform_int_distribution<unsigned long long> distr, mt19937_64* gen){
	return ((((uint128) distr(*gen)) << 64) | (uint128) distr(*gen));
}


void print_uint(uint128 n){
	if (n == 0){
		putchar(' ');
		return;
	}
	print_uint(n/digitRep);
	putchar(n%digitRep + '0');
}

void print_uintR(rElt a){
	cout <<"("; print_uint(a.c[0]); cout<<", "; print_uint(a.c[1]); cout<<", "; print_uint(a.c[2]); cout<<", "; print_uint(a.c[3]); cout<<")"<<endl;
}

void print_ver(int round, int ni, uint128** poly, uint128 extrap_val, long lev = LV){
	cout << "check for round "<< round << " failed when ni was " << ni << endl;
	cout << "extrap_val was ";print_uint(extrap_val); cout << endl;
	cout << "poly[round][0] was ";print_uint(poly[round][0]);
	cout << " and poly[round][1] was ";print_uint(poly[round][1]);
	cout << " and their sum was ";print_uint(myMod(poly[round][0] + poly[round][1], lev)); cout << endl;
	//exit(1);
}



/**************************/
/* basic ring operations  */
/**************************/


// equality test (return 1 if equal, 0 if not equal)
bool eqTest(rElt a, rElt b){
	for (int i = 0; i < DIM; ++i)
		if (a.c[i] != b.c[i])
			return 0;

	return 1;
}

// embedd Constant (in Mont form) to RingElt (preserve level)
rElt embC(uint128 xm){
	rElt res = ZERO;
	res.c[0] = xm;
	return res;
}


rElt myModPER(rElt x){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = myModPE(x.c[i]);
	return res;
}

rElt myModR(rElt x, long lev = LV){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = myMod(x.c[i], lev);
	return res;
}

rElt conv_to_monR(rElt x, long lev = LV){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = conv_to_mon(x.c[i], lev);
	return res;
}

rElt conv_from_monR(rElt xm, long lev = LV){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = conv_from_mon(xm.c[i], lev);
	return res;
}

// ring elt is in mont form, constant is in mont form
rElt addC(rElt xm, uint128 cm, long lev = LV){
	rElt res = xm;
	res.c[0] = myMod(xm.c[0] + cm, lev);
	return res;
}

rElt mulC(rElt am, uint128 cm, long lev = LV){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = myModMult(am.c[i], cm, lev);
	return res;
}

rElt addR(rElt am, rElt bm, long lev = LV){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = myMod(am.c[i] + bm.c[i], lev);
	return res;
}

rElt subR(rElt am, rElt bm, long lev = LV){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = myMod(am.c[i] + PRIMES[lev]-bm.c[i], lev);
	return res;
}

//// for 4 dim
//rElt myModMultR(rElt xm, rElt ym, long lev = LV){
//	rElt res;
//	uint128 tmp1, tmp2;
//	tmp1 = myMod(myModMult(xm.c[0], ym.c[0], lev) + myModMult(3*xm.c[3], ym.c[1], lev), lev);
//	tmp2 = myMod(myModMult(3*xm.c[2], ym.c[2], lev) + myModMult(3*xm.c[1], ym.c[3], lev), lev);
//	res.c[0] = myMod(tmp1 + tmp2, lev);
//
//	tmp1 = myMod(myModMult(xm.c[0], ym.c[1], lev) + myModMult(3*xm.c[3], ym.c[2], lev), lev);
//	tmp2 = myMod(myModMult(3*xm.c[2], ym.c[3], lev) + myModMult(xm.c[1], ym.c[0], lev), lev);
//	res.c[1] = myMod(tmp1 + tmp2, lev);
//
//	tmp1 = myMod(myModMult(xm.c[0], ym.c[2], lev) + myModMult(3*xm.c[3], ym.c[3], lev), lev);
//	tmp2 = myMod(myModMult(xm.c[2], ym.c[0], lev) + myModMult(xm.c[1], ym.c[1], lev), lev);
//	res.c[2] = myMod(tmp1 + tmp2, lev);
//
//	tmp1 = myMod(myModMult(xm.c[0], ym.c[3], lev) + myModMult(xm.c[3], ym.c[0], lev), lev);
//	tmp2 = myMod(myModMult(xm.c[2], ym.c[1], lev) + myModMult(xm.c[1], ym.c[2], lev), lev);
//	res.c[3] = myMod(tmp1 + tmp2, lev);
//
//	return res;
//}

// for 2 dim : x^2 + 1
rElt myModMultR(rElt xm, rElt ym, long lev = LV){
	rElt res;

//	NTL_EXEC_RANGE(2, first, last);
//	for (int i = first; i < last; ++i){
//		res.c[i] = myMod(myModMult(xm.c[0], ym.c[i], lev) + (1-i)*PRIMES[lev] + (2*i-1)*myModMult(xm.c[1], ym.c[1-i], lev), lev);
//	}
//	NTL_EXEC_RANGE_END

	res.c[0] = myMod(myModMult(xm.c[0], ym.c[0], lev) + PRIMES[lev] - myModMult(xm.c[1], ym.c[1], lev), lev);
	res.c[1] = myMod(myModMult(xm.c[0], ym.c[1], lev) + myModMult(xm.c[1], ym.c[0], lev), lev);
	return res;
}


//// for 1 dim
//rElt myModMultR(rElt xm, rElt ym, long lev = LV){
//	rElt res;
//	res.c[0] = myMod(myModMult(xm.c[0], ym.c[0], lev));
//
//	return res;
//}

rElt div_pR(rElt xp){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = div_p(xp.c[i]);
	return res;
}

//rElt rand_128R(uniform_int_distribution<unsigned long long> distr, mt19937_64* gen){
rElt rand_128R(){
	rElt res;
	for (int i = 0; i < DIM; ++i)
		res.c[i] = rand()%PRIME;
//		res.c[i] = rand_128(distr, gen);
	return res;
}

void print_verR(int round, int ni, rElt** poly, rElt extrap_val, long lev = LV){
	cout << "check for round "<< round << " failed when ni was " << ni << endl;
	cout << "extrap_val was ";print_uintR(extrap_val); cout << endl;
	cout << "poly[round][0] was ";print_uintR(poly[round][0]);
	cout << " and poly[round][1] was ";print_uintR(poly[round][1]);
	cout << " and their sum was "; print_uintR(addR(poly[round][0], poly[round][1])); cout << endl;
	//exit(1);
}

// Initialize parameters
void init_params(){
	PRIMES[0] =_P[0] = 1;
	for (long i = 1; i < E+1; ++i){
		PRIMES[i] = PRIMES[i-1] * PRIME;
		_P[i] = -invModPo2(PRIMES[i], 128);
	}

	MASK127 = myPow(2, 127) - 1;
	MASK64 = myPow(2, 64) - 1;

	uint128 R = myModPE(myPow(2, 127)); 		// R = 2^128 (mod N)
	R = myModPE(R << 1);
	uint128 index = R;
	R2[E] = 0;
	for (int i = 0; i < 128; ++i){
		if (index&1)
			R2[E] = myModPE(R2[E] + R);
		index >>= 1;
		R = myModPE(R << 1);
	}
	for (long i = 1; i < E; ++i){
		R2[E-i] = R2[E-i+1]%PRIMES[E-i];
	}

	uint128 q = myPow(2, 127)/PRIME;
	uint128 r = myPow(2, 127)%PRIME;
	NUMER = 2*q + 1 + (2*r > PRIME);

	for (long i = 0; i < PRIME; ++i){
		CST[i] = new uint128[E+1]();
		CSTR[i] = new rElt[E+1]();
		invCST[i] = new uint128[E+1]();
		for (long j = 0; j < E+1; ++j){
			CST[i][j] = conv_to_mon(i, j);
			CSTR[i][j] = embC(CST[i][j]);
			if ((i != 0) && (j!=0))
				invCST[i][j] = inv(CST[i][j], j);
		}
	}

	LV = E;

	for (long i = 0; i < E+1; ++i){
		LOG_ep[i] = 1;
		while (myPow(2,LOG_ep[i]) < i*PRIME){
			LOG_ep[i]++;
		}
		LOG_sqr_ep[i] = (LOG_ep[i])/2;
		LOG_rem[i] = LOG_ep[i] - LOG_sqr_ep[i];
	}

	for (long i = 0; i < DIM; ++i){
		ONE.c[i] = 0 + (i == 0);
		ZERO.c[i] = 0;
	}

	GAMMA = (double) ETA/log2(PRIME) + 0.5;

	cout << "init param complete!"<<endl;
}

// simple rounding without LDpoly
// input&output are in Montgomery form
rElt simRoundingR(rElt input, long lev = LV){
	rElt a = conv_from_monR(input, lev);
	uint128 a0 = a.c[0]%PRIME;
	if (a0 > (PRIME-1)/2)
		return conv_to_monR(addC(input, CST[PRIME - a0][lev], lev), lev);
	else
		return conv_to_monR(addC(input, PRIMES[lev]-CST[a0][lev], lev), lev);
}



/***************************************************************************************************************/
/* ZZ functions for generation of LDpoly and correctness check. (It is not used if one already has LDpoly file) *
/***************************************************************************************************************/

// Convert ZZ elt to uint128, assume that elt is at most 128bit.
uint128 conv128(ZZ in){
	ZZ x = in;
	uint128 res = 0;
	uint128 tmp2;
	long tmp;
	long pow = 0;

	while(x != 0){
		conv(tmp, x%2);
		tmp2 = tmp;
		tmp2 <<= pow;
		res += tmp2;
		x >>= 1;
		pow++;
	}

	return res;
}

// Extended Euclidean Algorithm for inverse mod
// u1 * x + u2 * v3 = gcd(x, v3) = u3	where v3 = mod
ZZ invZZ(ZZ x, ZZ mod){
	ZZ u1 = ZZ(1);
	ZZ u2 = ZZ(0);
	ZZ u3 = ZZ(x);
	ZZ v1 = ZZ(0);
	ZZ v2 = ZZ(1);
	ZZ v3 = mod;
	ZZ q, t1, t2, t3;

	do{
		q = u3 / v3;
		t1 = u1 - q*v1;
	    t2 = u2 - q*v2;
	    t3 = u3 - q*v3;
	    u1 = v1;
	    u2 = v2;
	    u3 = v3;
	    v1 = t1;
	    v2 = t2;
	    v3 = t3;
	}while (v3!=0);

	if (u3 != ZZ(1)){
		cout << "No inverse!"<<endl;
		return ZZ(0);
	}


	return u1 % mod;
}

ZZ myZZPow(ZZ x, ZZ pow, ZZ mod){
	ZZ res;
	if (pow == ZZ(0)) return ZZ(1);
	if (pow == ZZ(1)) return x;
	if ((pow&1) == 0){
		res = myZZPow(x, (pow >> 1), mod);
		return (res*res)%mod;
	}
	else
		return (myZZPow(x, pow-1, mod)*x)%mod;
}

// Gets coeffs of LDPoly from file, stores it to poly.
void LowDigitPolyIn(uint128* poly, long e){
	string filename = "LDpolyE=" + to_string(e);
	long end = (e-1)*(PRIME-1)+1;
	ifstream file(filename);
	string line;
	if (file.fail())
		cout << "No input" << endl;
	for (long i = 0; i < end; ++i){
		getline(file, line, ',');
		poly[i] = strtoull((char*) line.c_str(), NULL, 10);
		poly[i] <<= 64;
		getline(file, line, '\n');
		poly[i] += strtoull((char*) line.c_str(), NULL, 10);
	}
	file.close();
}

// Outputs coeffs of LDPoly to file
void LowDigitPolyOut(uint128* res, long e){
	string filename = "LDpolyE=" + to_string(e);
	long end = (e-1)*(PRIME-1)+1;
	ofstream myfile (filename);
	if (myfile.is_open()){
		for (long i = 0; i < end; ++i){
			myfile << (uint64) (res[i]>>64) <<", ";
			myfile << (uint64) (res[i]&MASK64) <<"\n";
		}
		myfile.close();
	}
	else
		cout << "Unable to open file";
}

// returns a(m) for each m in [PRIME, (e-1)(PRIME-1)+1] using ZZ
// res = ZZ[(e-1)(p-1)+1 -p +1][2]
// each of the form (p-adic val of a(m), remaiining) i.e. returns (n_i, c_i) if a(i) is of the form p^(n_i) * c_i where c_i not divisible by p.
void LDPcoeff_am_ZZ(ZZ** res, long e){
/// Initialize
	ZZ mod = ZZ(power(ZZ(PRIME), e));
	long st = PRIME;
	long end = (e-1)*(PRIME-1)+1;
	ZZ** am = new ZZ*[end-st+1];
	for (long i = 0; i < end-st+1; ++i){
		am[i] = new ZZ[2]();
		am[i][0] = 1;
	}

/// When m = PRIME, a(m) = PRIME.
	am[0][0] = 1;
	am[0][1] = 1;

/// When m > PRIME
	for (long i = 1; i < end-st+1; ++i){
		long m = i + st;
		long q = m/PRIME;
		ZZ numer = ZZ(1);
		ZZ denom = ZZ(1);
		ZZ* summand = new ZZ[q]();						// summand of each a(i)

		for (long j = m-1; j >= PRIME; --j){				// calculate numerators
			numer = numer * j;
			if (j % PRIME == 0)
				summand[(j/PRIME)-1] = numer;
		}

		for (long j = 1; j <= m-PRIME; ++j){				// calculate denominators
			denom = denom * j;
			if ((m-j) % PRIME == 0)
				summand[((m-j)/PRIME)-1] = summand[((m-j)/PRIME)-1]/denom;
		}

		if (m%PRIME == 0)								// manage exceptional case when m = q*PRIME
			summand[q-1] = 1;

		for (long j = 0; j < q; ++j){					// sum all the summand to get a(i)
			if ((m-(j+1)*PRIME)%2 == 0)
				am[i][1] += summand[j];
			else
				am[i][1] -= summand[j];
		}

		if (am[i][1] != 0){								// represent a(i) by power of PRIME and others
			while((am[i][1]%PRIME) == 0){
				am[i][1] = am[i][1]/PRIME;
				am[i][0] += 1;
			}
		}

		delete [] summand;
	}

	for (long i = 0; i < end-st+1; ++i){
		res[i][0] = am[i][0];
		res[i][1] = am[i][1]%mod;
	}

	for (long i = 0; i < end-st+1; ++i)
		delete [] am[i];
	delete [] am;
}

// res = ZZ[(e-1)(p-1)+1 -p +1][2]
// returns (log_p(m!), 1/(m! without p)) for each m in [p, (e-1)(p-1)+1] (mod PRIME^e)
void mFactInvs(ZZ** res, long e){
	/// Initialize
	ZZ mod = ZZ(power(ZZ(PRIME), e));
	long st = PRIME;
	long end = (e-1)*(PRIME-1)+1;
	for (long i = 0; i < end-st+1; ++i){
		res[i][0] = ZZ(0);
		res[i][1] = ZZ(1);
	}

	/// fist calculate (st)!
	for (long i = 1; i < st+1; ++i){
		if (i%PRIME == 0){
			res[0][0] += 1;
			res[0][1] = (res[0][1] * (i/PRIME))%mod;
		}
		else
			res[0][1] = (res[0][1] * i)%mod;
	}

	/// use (st)! to calculate other factorials until (end)!
	for (long i = 1; i < end-st+1; ++i){
		if ((i+st) % (PRIME*PRIME) == 0){
			res[i][0] = res[i-1][0] + 2;
			res[i][1] = (res[i-1][1] * ((i+st)/(PRIME*PRIME)))%mod;
		}
		else if ((i+st) % PRIME == 0){
			res[i][0] = res[i-1][0] + 1;
			res[i][1] = (res[i-1][1] * ((i+st)/PRIME))%mod;
		}
		else{
			res[i][0] = res[i-1][0];
			res[i][1] = (res[i-1][1] * (i+st))%mod;
		}
	}

	/// take Inverse
	for (long i = 0; i < end-st+1; ++i)
		res[i][1] = invZZ(res[i][1], mod);
}

// returns the expansion results of x(x-1)...(x-(st-1)) to x(x-1)...(x-(end-1))
// res[i][j] has degree j coeffs of i-th poly expansion whose degree is i+st.
// Assume that res is initialized to 0.
void genPolys(ZZ** res, long e){
	long st = PRIME;
	long end = (e-1)*(PRIME-1)+1;
	ZZ mod = ZZ(power(ZZ(PRIME), e));
	ZZ* a = new ZZ[end];
	for (long i = 0; i < end; ++i)
		a[i] = ZZ(-i+(PRIME-1)/2)%mod;

	// coeffs of b_0 + b_1*x + ... + b_deg*x^st
	res[0][0] = a[0];
	res[0][1] = ZZ(1);
	for (long i = 1; i < st; ++i){
		res[0][i+1] = res[0][i];
		for (long j = i; j > 0; --j)
			res[0][j] = (res[0][j-1] + (a[i]*res[0][j]))%mod;
		res[0][0] = (res[0][0] * a[i])%mod;
	}

	// other coeffs
	for (long i = 1; i < end-st+1; ++i){
		for (long j = st + i; j > 0; --j)
			res[i][j] = (res[i-1][j-1] + a[st+i-1]*res[i-1][j])%mod;
		res[i][0] = (res[i-1][0]*a[st+i-1])%mod;
	}

	delete [] a;
}

// eval coeffs of LowDigitRemoval Poly of degree < PRIME * e  and stores it to file.
// valid only for e > 1.
void genLowDigitPoly(long e){
	long st = PRIME;
	long end = (e-1)*(PRIME-1)+1;
	uint128* res = new uint128[end]();
	//uint128* res = new uint128[end]();
	ZZ mod = ZZ(power(ZZ(PRIME), e));

	ZZ* coeff = new ZZ[end+1];
	ZZ** fact = new ZZ*[end-st+1];
	ZZ** coeff_ams = new ZZ*[end-st+1];
	ZZ** polys = new ZZ*[end-st+1];
	for (long i = 0; i < end-st+1; ++i){
		fact[i] = new ZZ[2]();
		coeff_ams[i] = new ZZ[2]();
		polys[i] = new ZZ[end+1]();
	}

	//cout << "compute (m!)inv start"<<endl;
	mFactInvs(fact, e);

	//cout << "coeff_am start"<<endl;
	LDPcoeff_am_ZZ(coeff_ams, e);

	for (long i = 0; i < end-st+1; ++i){
		if (coeff_ams[i][0] >= fact[i][0])
			coeff_ams[i][0] -= fact[i][0];

		coeff_ams[i][1] = (coeff_ams[i][1] * fact[i][1])%mod;
		coeff_ams[i][0] = (myZZPow(ZZ(PRIME), coeff_ams[i][0], mod) * coeff_ams[i][1])%mod;
	}

	//cout << "evalPoly start"<<endl;
	genPolys(polys, e);

	for (long j = 0; j < end+1; ++j)
		for (long i = 0; i < end-st+1; ++i)
			coeff[j] = (coeff[j] + (polys[i][j] * coeff_ams[i][0]))%mod;

	for (long j = 0; j < end; ++j)
		res[j] = conv128(coeff[j+1]);


	LowDigitPolyOut(res, e);


	for (long i = 0; i < end-st+1; ++i){
		delete [] fact[i];
		delete [] coeff_ams[i];
		delete [] polys[i];
	}
	delete [] fact;
	delete [] coeff_ams;
	delete [] polys;
	delete [] res;
}

// evaluate polynomial of zero constant at given input (in/out not in Montgomery form)
// only for correctness check
uint128 evalPoly(uint128* coeff, uint128 input, long deg, long e){
	uint128 res = 0;
	uint128 tmp = 1;
	tmp = conv_to_mon(tmp, e);
	uint128 inputm = conv_to_mon(input, e);

	for (long i = 0; i < deg; ++i){
		tmp = myModMult(tmp, inputm, e);
		res = myMod(res + myModMult(tmp, conv_to_mon(coeff[i], e), e), e);
	}

	return conv_from_mon(res, e);
}

// evaluate polynomial at given input (in/out in Montgomery form)
// only for correctness check
rElt evalPolyR(rElt* coeffm, rElt xm, long deg, long lev = LV){
	rElt res = coeffm[0];
	rElt tmp = ONE;
	tmp = conv_to_monR(tmp, lev);

	for (long i = 1; i < deg+1; ++i){
		tmp = myModMultR(tmp, xm, lev);
		res = addR(res, myModMultR(tmp, coeffm[i], lev), lev);
	}

	return res;
}




/****************************************************************************************/
/* functions for GKR protocol // All input & output of function are in Montgomery form  *
/****************************************************************************************/


//computes chi_v(r), where chi is the Lagrange polynomial that takes
//boolean vector v to 1 and all other boolean vectors to 0. (we view v's bits as defining a boolean vector. n is dimension of this vector.)
//all arithmetics are mod prime^lev, input&output are in Motgomery form
uint128 chi(uint128 n, uint128 v, uint128* rm, long lev = LV){
	uint128 x = v;
	uint128 c = CST[1][lev];
	for(uint128 i = 0; i < n; i++){
		if(x&1)
			c = myModMult(c, rm[i], lev);
		else
			c = myModMult(c, myMod(CST[1][lev]+PRIMES[lev]-rm[i], lev), lev);
		x = x >> 1;
	}
	return c;
}

//computes chi_v(r), where chi is the Lagrange polynomial that takes
//boolean vector v to 1 and all other boolean vectors to 0. (we view v's bits as defining a boolean vector. n is dimension of this vector.)
//all arithmetics are mod prime^lev, input&output are in Motgomery form
rElt chiR(uint128 n, uint128 v, rElt* rm, long lev = LV){
	uint128 x = v;
	rElt c = CSTR[1][lev];
	for(uint128 i = 0; i < n; i++){
		if(x&1)
			c = myModMultR(c, rm[i], lev);
		else
			c = myModMultR(c, subR(CSTR[1][lev], rm[i], lev), lev);
		x = x >> 1;
	}
	return c;
}

//evaluates V_i polynomial at location r. V_i is described in GKR08;
//it is the multi-linear extension of the vector of gate values at level i of the circuit
//ni: number of gates in level_i, mi: log (ni), dimension of vector
//all arithmetics are mod prime^lev, input&output are in Motgomery form
uint128 evaluate_V_i_stream(int mi, int ni, uint128* level_i, uint128* rm, long lev = LV){
	uint128 ans = 0;
	for (uint128 k = 0; k < ni; ++k)
		ans = myMod(ans + myModMult(level_i[k], chi(mi, k, rm, lev), lev), lev);
	return ans;
}

//(Lagrangian) extrapolation of the polynomial implied by vector vec of length n to location r
//all arithmetics are mod prime^lev, input&output are in Motgomery form
uint128 extrap(uint128 n, uint128* vec, uint128 rm, long lev = LV){
	uint128 res = 0;
	uint128 mult = CST[1][lev];
	if (PRIME <= n)
		cout << "extrap failed, because of small prime!" << endl;
	if (conv_from_mon(rm, lev) < n)
		cout << "extrap error, because of the same pt!" << endl;
	for(long i = 0; i < n; ++i){
		mult = CST[1][lev];
		for(long j = 0; j < n; ++j){
			if (i!=j)
				mult = myModMult(myModMult(mult, myMod(rm+PRIMES[lev]-CST[j][lev], lev), lev), inv(myMod(CST[i][lev]+PRIMES[lev]-CST[j][lev], lev), lev), lev);
		}
		res = myMod(res + myModMult(mult, vec[i], lev), lev);
	}
	return res;
}


//(Lagrangian) extrapolation of the polynomial implied by vector vec of length n to location r
//all arithmetics are mod prime^lev, input&output are in Motgomery form
rElt extrapR(uint128 n, rElt* vec, rElt rm, long lev = LV){
	rElt res = ZERO;
	rElt mult = CSTR[1][lev];
	if (PRIME < n)
		cout << "extrap failed, because of small prime!" << endl;

	for(long i = 0; i < n; ++i){
		mult = CSTR[1][lev];
		for(long j = 0; j < n; ++j){
//			if (i!=j)
//				mult = mulC(myModMultR(mult, addC(rm, PRIMES[lev]-CST[j][lev], lev), lev), inv(myMod(CST[i][lev]+PRIMES[lev]-CST[j][lev], lev), lev), lev);
			if (i < j)
				mult = mulC(myModMultR(mult, addC(rm, PRIMES[lev]-CST[j][lev], lev), lev), myMod(PRIMES[lev]-invCST[j-i][lev], lev), lev);
			else if (i > j)
				mult = mulC(myModMultR(mult, addC(rm, PRIMES[lev]-CST[j][lev], lev), lev), invCST[i-j][lev], lev);
		}
		res = addR(res, myModMultR(mult, vec[i], lev), lev);
	}

	return res;
}

////(Lagrangian) extrapolation of the polynomial implied by vector vec of length n to location r
////all arithmetics are mod prime^lev, input&output are in Motgomery form
//rElt extrapR_old(uint128 n, rElt* vec, rElt rm, long lev = LV){
//	rElt res = ZERO;
//	rElt mult = CSTR[1][lev];
//	if (PRIME*lev < n)
//		cout << "extrap failed, because of small prime!" << endl;
//
//	for(long i = 0; i < n; ++i){
//		mult = CSTR[1][lev];
//		for(long j = 0; j < n; ++j){
//			if (i!=j)
//				mult = myModMultR(myModMultR(mult, subR(rm, CSTR[j][lev], lev), lev), invR(subR(CSTR[i][lev], CSTR[j][lev], lev), lev), lev);
//		}
//		res = addR(res, myModMultR(mult, vec[i], lev), lev);
//	}
//
//	return res;
//}


//(Lagrangian) extrapolation of the polynomial implied by vector vec of length n to location r
//all arithmetics are mod prime^lev, input&output are in Motgomery form
//barycentric form using precomputed lagW values, and # of interpolation points are fixed to lev*PRIME + 1 !
//rElt extrapRbary(rElt* vec, rElt rm, long lev = LV){
//	uint128 n = lev * PRIME;
//	rElt numer = ZERO;
//	rElt denom = ZERO;
//	rElt tmp;
//
//	for(long j = 0; j < n; ++j){
//		tmp = myModMultR(lagW[j][lev], invR(subR(rm, CSTR[j][lev], lev), lev), lev);
//		numer = addR(numer, myModMultR(tmp, vec[j], lev), lev);
//		denom = addR(denom, tmp, lev);
//	}
//
//	return myModMultR(numer, invR(denom, lev), lev);
//}


//fills in high-order variable xi wih ri
//all arithmetics are mod prime^lev, input&output are in Motgomery form
void updateV(uint128* V, uint128 num_new, uint128 ri, long lev = LV){
	for(int i = 0; i < num_new; ++i)
		V[i] = myMod(myModMult(V[i], CST[1][lev]+PRIMES[lev]-ri, lev) + myModMult(V[i+num_new], ri, lev), lev);
}


//fills in high-order variable xi wih ri
//all arithmetics are mod prime^lev, input&output are in Motgomery form
void updateVR(rElt* V, uint128 num_new, rElt ri, long lev = LV){
	for(uint128 i = 0; i < num_new; ++i)
		V[i] = addR(myModMultR(V[i], subR(CSTR[1][lev], ri, lev), lev), myModMultR(V[i+num_new], ri, lev), lev);
}


//fills in high-order variable xi wih ri
//update V from the middle pt (rightest pt is 0 th)
//all arithmetics are mod prime^lev, input&output are in Motgomery form
void updateVRmid(rElt* V, uint128 num_new, rElt ri, long mid, long lev = LV){
	uint128 one = (1 << mid);
	uint128 ones = one - 1;
	for(uint128 i = 0; i < num_new; ++i){
		uint128 ip = (i & ones) + ((i >> mid) << (mid+1));
		V[i] = addR(myModMultR(V[ip], subR(CSTR[1][lev], ri, lev), lev), myModMultR(V[ip+one], ri, lev), lev);
	}

}


// outputs the same value as evaluate_V_i_stream, but much faster than it using more space.
//ni: number of gates in level_i, mi: log (ni), dimension of vector
//all arithmetics are mod prime^lev, input&output are in Motgomery form
uint128 evaluate_V_i(int mi, int ni, uint128* level_i, uint128* r, long lev = LV){
	uint128* V = new uint128[ni]();
	for (int i = 0; i < ni; ++i)
		V[i] = level_i[i];
	uint128 pow = myPow(2, mi-1);
	for (int i = mi-1; i >= 0; --i){
		updateV(V, pow, r[i], lev);
		pow >>= 1;
	}

	uint128 ans = V[0];
	delete [] V;
	return ans;
}


// outputs the same value as evaluate_V_i_stream, but much faster than it using more space.
//ni: number of gates in level_i, mi: log (ni), dimension of vector
//all arithmetics are mod prime^lev, input&output are in Motgomery form
rElt evaluate_V_iR(int mi, int ni, rElt* level_i, rElt* r, long lev = LV){
	rElt* V = new rElt[ni]();
	for (int i = 0; i < ni; ++i)
		V[i] = level_i[i];
	uint128 pow = myPow(2, mi-1);
	for (int i = mi-1; i >= 0; --i){
		updateVR(V, pow, r[i], lev);
		pow >>= 1;
	}

	rElt ans = V[0];
	delete [] V;
	return ans;
}



//sets betavals(p) = \prod_{i=0}^{d-1} (zipi + (1-zi)(1-pi)) where p is a binary vector!
//all arithmetics are mod prime^lev, input&output are in Motgomery form
void initialize_betavals(uint128* betavals, int d, uint128* z, long lev = LV){
	betavals[0]=CST[1][lev];
	uint128 zval;
	int two_to_k = 1;
	uint128 oldval;
	for(int k = 0; k < d; ++k){
		zval = z[k];
		for(int i = 0; i < two_to_k; ++i){
			oldval = betavals[i];
			betavals[i] = myModMult(oldval, myMod(CST[1][lev]+PRIMES[lev]-zval, lev), lev);
			betavals[i + two_to_k] = myModMult(oldval, zval, lev);
		}
		two_to_k = two_to_k * 2;
	}
}

//sets betavals(p) = \prod_{i=0}^{d-1} (zipi + (1-zi)(1-pi)) where p is a binary vector!
//all arithmetics are mod prime^lev, input&output are in Motgomery form
void initialize_betavalsR(rElt* betavals, int d, rElt* z, long lev = LV){
	betavals[0]=CSTR[1][lev];
	rElt zval;
	int two_to_k = 1;
	rElt oldval;
	for(int k = 0; k < d; ++k){
		zval = z[k];
		for(int i = 0; i < two_to_k; ++i){
			oldval = betavals[i];
			betavals[i] = myModMultR(oldval, subR(CSTR[1][lev], zval, lev), lev);
			betavals[i + two_to_k] = myModMultR(oldval, zval, lev);
		}
		two_to_k = two_to_k << 1;
	}
}


// evaluate beta(z,r), d: num of vars in z or r
rElt evaluate_beta_fast(int d, rElt* z, rElt* r, long lev = LV){
	rElt ans = ZERO;
	ans.c[0] = CST[1][lev];
	for(int i = 0; i < d; i++)
		ans = addR(ans, addR(myModMultR(r[i], z[i], lev), myModMultR(addC(r[i], PRIMES[lev] - CST[1][lev], lev), addC(z[i], PRIMES[lev] - CST[1][lev], lev), lev), lev), lev);

	return ans;
}


// output 'num_new' number of updated betavals (without computing inverse)
//all arithmetics are mod prime^lev, input&output are in Motgomery form
void update_betavals(uint128* betavals, int num_new, uint128 rval, long lev = LV){
	for(int i = 0; i < num_new; ++i)
		betavals[i] = myMod(myModMult(betavals[i], myMod(CST[1][lev]+PRIMES[lev]-rval, lev), lev) + myModMult(betavals[i+num_new], rval, lev), lev);
}


// output 'num_new' number of updated betavals (without computing inverse)
//all arithmetics are mod prime^lev, input&output are in Motgomery form
void update_betavalsR(rElt* betavals, int num_new, rElt rval, long lev = LV){
	for(int i = 0; i < num_new; ++i)
		betavals[i] = addR(myModMultR(betavals[i], subR(CSTR[1][lev], rval, lev), lev), myModMultR(betavals[i+num_new], rval, lev), lev);
}


//V is supposed to be list of vals at [layer i+1],
//d is log of number of gates, ni is number of gates at [layer i]
uint128 sum_check_bin_tree(uint128* V, uint128 ri, int d, int ni, int* com_ct, int* rd_ct, uint128*r, uint128** poly, uint128* betavals, uint128* z, long lev = LV)
{
	// initialize r & poly & betavals
	for(int i = 0; i <= d; i++){
		r[i] = rand() + 3;
		if (r[i]%PRIME == 0)
			r[i]++;
		r[i] = conv_to_mon(r[i], lev);
	}

	for(int i = 0; i < d; i++)
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = 0;
	*com_ct = *com_ct+3*d+2;
	*rd_ct = *rd_ct+d+1;

	initialize_betavals(betavals, d, z, lev);
	int num_terms = ni;
	uint128 beta2, V2;

	// modified sum-check without inverse
	for(int round = 0; round < d; round++)
	{
		uint128 hft = num_terms >> 1;
		for(int j = 0; j < num_terms; j++)
		{
			if(j & (num_terms >> 1))
			{
				poly[round][1] = myMod(poly[round][1] + myModMult(betavals[j], myMod( V[(j<<1)] + V[(j<<1)+1])));
				beta2 = myMod(myMod(2*betavals[j]) + PRIMES[lev]-betavals[j - (num_terms>>1)]);
				V2 = myMod(myMod(myMod(2*V[(j<<1)]) + PRIMES[lev]-V[((j-hft)<<1)]) + myMod(myMod(2*V[(j<<1)+1]) + PRIMES[lev]-V[((j-hft)<<1)+1]));
				poly[round][2] = myMod(poly[round][2] + myModMult(beta2, V2));
			}
			else
			{
				poly[round][0] = myMod(poly[round][0] + myModMult(betavals[j], myMod( V[(j<<1)] + V[(j<<1)+1])));
			}
		}

		num_terms = num_terms >> 1;
		update_betavals(betavals, num_terms, r[d-round]);
		updateV(V, num_terms << 1, r[d-round]);
	}

	// Verifier's check
	if(myMod(poly[0][0] + poly[0][1]) != ri)
	{
		cout << "first check failed when ni was " << ni << endl;
		cout << "ri was ";print_uint(ri);cout << endl;
		cout << "poly[0][0] was ";print_uint(poly[0][0]);
		cout << " and poly[0][1] was ";print_uint(poly[0][1]);
		cout << " and their sum was ";print_uint(myMod(poly[0][0] + poly[0][1])); cout << endl;
		//exit(1);
	}

	uint128 extrap_val = extrap(3, poly[0], r[d]);
	for(int round = 1; round < d; round++){
		if(myMod(poly[round][0] + poly[round][1]) != extrap_val)
			print_ver(round, ni, poly, extrap_val);
	 	extrap_val = extrap(3, poly[round], r[d-round]);
	 }

	 //now P "tells" V \tilde{V}(p)  and V checks final message based on this
	 //i.e. V checks g_{d-1}(r) = beta(z, p) \tilde{V}(rd, ..., r1, r0).
	 //If so, V believes P as long as \tilde{V}(p) = extrap(V, 2, r)

	 uint128 correct_out = myModMult(betavals[0], myMod(V[0] + V[1]));
	 if(correct_out != extrap_val)
	 {
	 	cout << "correct_out != extrap_val. correct_out is ";
	 	print_uint(correct_out);
	 	cout << " and extrap_val is: ";
	 	print_uint(extrap_val);
	 	cout << endl;
	 	//exit(1);
	 }
	 return extrap(2, V, r[0]);		// final result after sum-check
}


//V is supposed to be list of vals at [layer i+1],
//d is log of number of gates, ni is number of gates at [layer i]
rElt sum_check_bin_treeR(rElt* V, rElt ri, int d, int ni, int* com_ct, int* rd_ct, rElt*r, rElt** poly, rElt* betavals, rElt* z, long lev = LV)
{
	// initialize r & poly & betavals
	for(int i = 0; i <= d; i++){
		r[i] = rand_128R();
		conv_to_monR(r[i], lev);
	}

	for(int i = 0; i < d; i++)
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = ZERO;
	*com_ct = *com_ct+3*d+2;
	*rd_ct = *rd_ct+d+1;

	initialize_betavalsR(betavals, d, z, lev);
	int num_terms = ni;
	rElt beta2, V2;

	// modified sum-check without inverse
	for(int round = 0; round < d; round++)
	{
		uint128 hft = num_terms >> 1;
		for(int j = 0; j < num_terms; j++)
		{
			if(j & (num_terms >> 1))
			{
				poly[round][1] = addR(poly[round][1], myModMultR(betavals[j], addR(V[(j<<1)], V[(j<<1)+1])));
				beta2 = subR(mulC(betavals[j], CST[2][lev]), betavals[j - (num_terms>>1)]);
				V2 = addR(subR(mulC(V[(j<<1)], CST[2][lev]), V[((j-hft)<<1)]), subR(mulC(V[(j<<1)+1], CST[2][lev]), V[((j-hft)<<1)+1]));
				poly[round][2] = addR(poly[round][2], myModMultR(beta2, V2));
			}
			else
			{
				poly[round][0] = addR(poly[round][0], myModMultR(betavals[j], addR(V[(j<<1)], V[(j<<1)+1])));
			}
		}

		num_terms = num_terms >> 1;
		update_betavalsR(betavals, num_terms, r[d-round]);
		updateVR(V, num_terms << 1, r[d-round]);
	}

	// Verifier's check
	if(!eqTest(addR(poly[0][0], poly[0][1]), ri))
	{
		cout << "first check failed when ni was " << ni << endl;
		cout << "ri was ";print_uintR(ri);cout << endl;
		cout << "poly[0][0] was ";print_uintR(poly[0][0]);
		cout << " and poly[0][1] was ";print_uintR(poly[0][1]);
		cout << " and their sum was ";print_uintR(addR(poly[0][0], poly[0][1])); cout << endl;
		//exit(1);
	}

	rElt extrap_val = extrapR(3, poly[0], r[d]);
	for(int round = 1; round < d; round++){
		if(!eqTest(addR(poly[round][0], poly[round][1]), extrap_val))
			print_verR(round, ni, poly, extrap_val);
	 	extrap_val = extrapR(3, poly[round], r[d-round]);
	 }

	 //now P "tells" V \tilde{V}(p)  and V checks final message based on this
	 //i.e. V checks g_{d-1}(r) = beta(z, p) \tilde{V}(rd, ..., r1, r0).
	 //If so, V believes P as long as \tilde{V}(p) = extrap(V, 2, r)

	 rElt correct_out = myModMultR(betavals[0], addR(V[0], V[1]));
	 if(!eqTest(correct_out, extrap_val))
	 {
	 	cout << "correct_out != extrap_val. correct_out is ";
	 	print_uintR(correct_out);
	 	cout << " and extrap_val is: ";
	 	print_uintR(extrap_val);
	 	cout << endl;
	 	//exit(1);
	 }
	 return extrapR(2, V, r[0]);		// final result after sum-check
}


//V0 is supposed to be list of vals in the matrix A, V1 is list of vals in the matrix B^T, d is log of number of gates at layer i,
//ni is number of gates at layer i, ri0 will be set as post-condition to claimed value of A(r) and ri1 to claimed value of B(r') for the relavant random positions r and r'
void sum_check_matmult(circ* c, uint128* V0, uint128* V1, uint128 ri, int d, int ni, int* com_ct,
int* rd_ct, uint128*r, uint128** poly, uint128* betavals, uint128* z, uint128* ri0, uint128* ri1, fptr in1matmult, fptr in2matmult, long lev)
{
	for(int i = 0; i < d; i++){
		r[i] = rand();
		if (r[i] %PRIME ==0)
			r[i]++;
		r[i] = conv_to_mon(r[i], lev);
	}

	for(int i = 0; i < d; i++)
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = 0;
	*com_ct = *com_ct+3*(2*d/3) + 4*d/3;
	*rd_ct = *rd_ct+d + 1;

	initialize_betavals(betavals, d, z);
	int num_terms = ni;
	uint128 betar;
	int logn = d/3;
	int n=myPow(2, logn);

	uint128 betaupdate;
	//set num_is to n if we're multiplying nxn matrices
	int num_is = n;
	int num_js = n;
	int num_ks = n;
	int ik;
	int jk;
	int ijk;

	uint128 multby0;
	uint128 multby1;
	uint128 multby2;

	uint128 tmp_beta2, tmp_v02, tmp_v12;
	uint128 tmp_beta3, tmp_v03, tmp_v13;

	for(int round = 0; round < logn; round++){
		for(int i = 0; i < num_is; i++){
			for(int k = 0; k < n; k++){
				ik = (i << logn) + k;
				multby0=multby1=multby2=0;
				tmp_beta2=tmp_v02=0;

				for(int j = 0; j < n; j++){
					jk = (j << logn)+k;
					ijk= (i << (2*logn)) + jk;

					if(i & (num_is >> 1)){
						multby1= myMod(multby1 + myModMult(betavals[ijk], V1[jk]));
						tmp_beta2 = myMod(myMod(2*betavals[ijk]) + PRIMES[lev]-betavals[ijk-((num_is>>1)<<(2*logn))]);
						tmp_v02 = myMod(myMod(2*V0[ik]) + PRIMES[lev]-V0[ik-((num_is>>1)<<logn)]);
						multby2 = myMod(multby2 + myModMult(tmp_beta2, V1[jk]));
					}
					else
						multby0 = myMod(multby0 + myModMult(betavals[ijk], V1[jk]));

				}//end j loop

				poly[round][0] = myMod(poly[round][0] + myModMult(V0[ik], multby0));
				poly[round][1] = myMod(poly[round][1] + myModMult(V0[ik], multby1));
				poly[round][2] = myMod(poly[round][2] + myModMult(tmp_v02, multby2));
			}//end k loop
		}//end i loop

		num_is = num_is >> 1;
		update_betavals(betavals, num_is*n*n, r[d-1-round]);
		updateV(V0, num_is * n, r[d-1-round]);
	}


	for(int round = logn; round < 2*logn; round++){
		for(int k = 0; k < n; k++){
			multby0=multby1=multby2=0;
			tmp_beta2=tmp_v12=0;

			for(int j = 0; j < num_js; j++){
				ik = k;
				jk = (j << logn)+k;
				ijk= jk;

				if(j & (num_js >> 1)){
					multby1= myMod(multby1 + myModMult(betavals[ijk], V1[jk]));
					tmp_beta2 = myMod(myMod(2*betavals[ijk]) + PRIMES[lev]-betavals[ijk-((num_js>>1)<<logn)]);
					tmp_v12 = myMod(myMod(2*V1[jk]) + PRIMES[lev]-V1[jk-((num_js>>1)<<logn)]);
					multby2 = myMod(multby2 + myModMult(tmp_beta2, tmp_v12));
				}
				else
					multby0 = myMod(multby0 + myModMult(betavals[ijk], V1[jk]));
			}//end j loop

			poly[round][0] = myMod(poly[round][0] + myModMult(V0[ik], multby0));
			poly[round][1] = myMod(poly[round][1] + myModMult(V0[ik], multby1));
			poly[round][2] = myMod(poly[round][2] + myModMult(V0[ik], multby2));
		}//end k loop
		num_js = num_js >> 1;
		update_betavals(betavals, num_js*n, r[d-1-round]);
		updateV(V1, num_js * n, r[d-1-round]);
	}//end round loop


	for(int round = 2*logn; round < 3*logn; round++)	{
		for(int k = 0; k < num_ks; k++){
			ik = k;
			jk = k;
			ijk= k;
			tmp_beta2 = tmp_v02 = tmp_v12 = 0;
			tmp_beta3 = tmp_v03 = tmp_v13 = 0;

			if(k & (num_ks >> 1)){
				tmp_beta2 = myMod(myMod(2*betavals[ijk]) + PRIMES[lev]-betavals[ijk-(num_ks>>1)]);
				tmp_beta3 = myMod(myMod(tmp_beta2 + betavals[ijk]) + PRIMES[lev]-betavals[ijk-(num_ks>>1)]);
				tmp_v02 = myMod(myMod(2*V0[ik]) + PRIMES[lev]-V0[ik-(num_ks>>1)]);
				tmp_v03 = myMod(myMod(tmp_v02 + V0[ik]) + PRIMES[lev]-V0[ik-(num_ks>>1)]);
				tmp_v12 = myMod(myMod(2*V1[jk]) + PRIMES[lev]-V1[jk-(num_ks>>1)]);
				tmp_v13 = myMod(myMod(tmp_v12 + V1[jk]) + PRIMES[lev]-V1[jk-(num_ks>>1)]);

				poly[round][1] = myMod(poly[round][1] + myModMult(betavals[ijk], myModMult(V0[ik], V1[jk])));
				poly[round][2] = myMod(poly[round][2] + myModMult(tmp_beta2, myModMult(tmp_v02, tmp_v12)));
				poly[round][3] = myMod(poly[round][3] + myModMult(tmp_beta3, myModMult(tmp_v03, tmp_v13)));
			}
			else
				poly[round][0] = myMod(poly[round][0] + myModMult(betavals[ijk], myModMult(V0[ik], V1[jk])));

		}//end k loop
		num_ks = num_ks >> 1;
		update_betavals(betavals, num_ks, r[d-1-round]);
		updateV(V0, num_ks, r[d-1-round]);
		updateV(V1, num_ks, r[d-1-round]);
	}//end round loop

	// ================== 3rd round end ==============//

//// Verifier's Check
	if (myMod(poly[0][0] + poly[0][1]) != ri)
	{
		cout << "first check failed in checking final layer when ni was " << ni << endl;
		cout << "ri was ";print_uint(ri);
		cout << "poly[0][0] was ";print_uint(poly[0][0]);
		cout << " and poly[0][1] was ";print_uint(poly[0][1]);
		cout << " and their sum was ";print_uint(myMod(poly[0][0] + poly[0][1]));
		cout << endl;
		//exit(1);
	}

	uint128 extrap_val = extrap( 3, poly[0], r[d-1]);
	for(int round = 1; round < 3*logn; round++)
	{
		if (myMod(poly[round][0] + poly[round][1]) != extrap_val)
			print_ver(round, ni, poly, extrap_val);

		if (round < 2*logn)
			extrap_val = extrap(3, poly[round], r[d-1-round]);
		else
			extrap_val = extrap(4, poly[round], r[d-1-round]);
	 }

	 //now P "tells" V \tilde{A}(r) and \tilde{B^T}(r') and V checks final message based on this
	 //i.e. V checks g_{d-1}(r) = beta(z, p) \tilde{A}(r_{d-1}, ..., r1, r0) \tilde{B^T}(r_{d-1}, ..., r0)
	 //If so, V believes P as long as \tilde{A}(r) and \tilde{B^T}(r') are as claimed

	 uint128 correct_out = myModMult(betavals[0], myModMult(V0[0], V1[0]));
	 if (correct_out != extrap_val)
	 {
	 	cout << "correct_out != extrap_val in check for final layer. correct_out is ";
	 	print_uint(correct_out);
	 	cout << " and extrap_val is: ";
	 	print_uint(extrap_val);
	 	cout << endl;
	 	//exit(1);
	 }

	 *ri0 = V0[0];
	 *ri1 = V1[0];
}


//V0 is supposed to be list of vals in the matrix A, V1 is list of vals in the matrix B^T, d is log of number of gates at layer i,
//ni is number of gates at layer i, ri0 will be set as post-condition to claimed value of A(r) and ri1 to claimed value of B(r') for the relavant random positions r and r'
void sum_check_matmultR(circ* c, rElt* V0, rElt* V1, rElt ri, int d, int ni, int* com_ct,
int* rd_ct, rElt*r, rElt** poly, rElt* betavals, rElt* z, rElt* ri0, rElt* ri1, fptr in1matmult, fptr in2matmult, long lev)
{
	for(int i = 0; i < d; i++){
		r[i] = conv_to_monR(rand_128R(), lev);
	}

	for(int i = 0; i < d; i++)
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = ZERO;

	*com_ct = *com_ct+3*(2*d/3) + 4*d/3;
	*rd_ct = *rd_ct+d + 1;

	initialize_betavalsR(betavals, d, z);
	int num_terms = ni;
	rElt betar;
	int logn = d/3;
	int n=myPow(2, logn);

	rElt betaupdate;
	//set num_is to n if we're multiplying nxn matrices
	int num_is = n;
	int num_js = n;
	int num_ks = n;
	int ik;
	int jk;
	int ijk;

	rElt multby0;
	rElt multby1;
	rElt multby2;

	rElt tmp_beta2, tmp_v02, tmp_v12;
	rElt tmp_beta3, tmp_v03, tmp_v13;

	for(int round = 0; round < logn; round++){
		for(int i = 0; i < num_is; i++){
			for(int k = 0; k < n; k++){
				ik = (i << logn) + k;
				multby0=multby1=multby2=ZERO;
				tmp_beta2=tmp_v02=ZERO;

				for(int j = 0; j < n; j++){
					jk = (j << logn)+k;
					ijk= (i << (2*logn)) + jk;

					if(i & (num_is >> 1)){
						multby1= addR(multby1, myModMultR(betavals[ijk], V1[jk]));
						tmp_beta2 = subR(mulC(betavals[ijk], CST[2][lev]), betavals[ijk-((num_is>>1)<<(2*logn))]);
						tmp_v02 = subR(mulC(V0[ik], CST[2][lev]), V0[ik-((num_is>>1)<<logn)]);
						multby2 = addR(multby2, myModMultR(tmp_beta2, V1[jk]));
					}
					else
						multby0 = addR(multby0, myModMultR(betavals[ijk], V1[jk]));

				}//end j loop

				poly[round][0] = addR(poly[round][0], myModMultR(V0[ik], multby0));
				poly[round][1] = addR(poly[round][1], myModMultR(V0[ik], multby1));
				poly[round][2] = addR(poly[round][2], myModMultR(tmp_v02, multby2));
			}//end k loop
		}//end i loop

		num_is = num_is >> 1;
		update_betavalsR(betavals, num_is*n*n, r[d-1-round]);
		updateVR(V0, num_is * n, r[d-1-round]);
	}


	for(int round = logn; round < 2*logn; round++){
		for(int k = 0; k < n; k++){
			multby0=multby1=multby2=ZERO;
			tmp_beta2=tmp_v12=ZERO;

			for(int j = 0; j < num_js; j++){
				ik = k;
				jk = (j << logn)+k;
				ijk= jk;

				if(j & (num_js >> 1)){
					multby1= addR(multby1, myModMultR(betavals[ijk], V1[jk]));
					tmp_beta2 = subR(mulC(betavals[ijk], CST[2][lev]), betavals[ijk-((num_js>>1)<<logn)]);
					tmp_v12 = subR(mulC(V1[jk], CST[2][lev]), V1[jk-((num_js>>1)<<logn)]);
					multby2 = addR(multby2, myModMultR(tmp_beta2, tmp_v12));
				}
				else
					multby0 = addR(multby0, myModMultR(betavals[ijk], V1[jk]));
			}//end j loop

			poly[round][0] = addR(poly[round][0], myModMultR(V0[ik], multby0));
			poly[round][1] = addR(poly[round][1], myModMultR(V0[ik], multby1));
			poly[round][2] = addR(poly[round][2], myModMultR(V0[ik], multby2));
		}//end k loop
		num_js = num_js >> 1;
		update_betavalsR(betavals, num_js*n, r[d-1-round]);
		updateVR(V1, num_js * n, r[d-1-round]);
	}//end round loop


	for(int round = 2*logn; round < 3*logn; round++)	{
		for(int k = 0; k < num_ks; k++){
			ik = k;
			jk = k;
			ijk= k;
			tmp_beta2 = tmp_v02 = tmp_v12 = ZERO;
			tmp_beta3 = tmp_v03 = tmp_v13 = ZERO;

			if(k & (num_ks >> 1)){
				tmp_beta2 = subR(mulC(betavals[ijk], CST[2][lev]), betavals[ijk-(num_ks>>1)]);
				tmp_beta3 = subR(addR(tmp_beta2, betavals[ijk]), betavals[ijk-(num_ks>>1)]);
				tmp_v02 = subR(mulC(V0[ik], CST[2][lev]), V0[ik-(num_ks>>1)]);
				tmp_v03 = subR(addR(tmp_v02, V0[ik]), V0[ik-(num_ks>>1)]);
				tmp_v12 = subR(mulC(V1[jk], CST[2][lev]), V1[jk-(num_ks>>1)]);
				tmp_v13 = subR(addR(tmp_v12, V1[jk]), V1[jk-(num_ks>>1)]);

				poly[round][1] = addR(poly[round][1], myModMultR(betavals[ijk], myModMultR(V0[ik], V1[jk])));
				poly[round][2] = addR(poly[round][2], myModMultR(tmp_beta2, myModMultR(tmp_v02, tmp_v12)));
				poly[round][3] = addR(poly[round][3], myModMultR(tmp_beta3, myModMultR(tmp_v03, tmp_v13)));
			}
			else
				poly[round][0] = addR(poly[round][0], myModMultR(betavals[ijk], myModMultR(V0[ik], V1[jk])));

		}//end k loop
		num_ks = num_ks >> 1;
		update_betavalsR(betavals, num_ks, r[d-1-round]);
		updateVR(V0, num_ks, r[d-1-round]);
		updateVR(V1, num_ks, r[d-1-round]);
	}//end round loop

	// ================== 3rd round end ==============//

//// Verifier's Check
	if (!eqTest(addR(poly[0][0], poly[0][1]), ri))
	{
		cout << "first check failed in checking final layer when ni was " << ni << endl;
		cout << "ri was ";print_uintR(ri);
		cout << "poly[0][0] was ";print_uintR(poly[0][0]);
		cout << " and poly[0][1] was ";print_uintR(poly[0][1]);
		cout << " and their sum was ";print_uintR(addR(poly[0][0], poly[0][1]));
		cout << endl;
		//exit(1);
	}

	rElt extrap_val = extrapR(3, poly[0], r[d-1]);
	for(int round = 1; round < 3*logn; round++)
	{
		if (!eqTest(addR(poly[round][0], poly[round][1]), extrap_val))
			print_verR(round, ni, poly, extrap_val);

		if (round < 2*logn)
			extrap_val = extrapR(3, poly[round], r[d-1-round]);
		else
			extrap_val = extrapR(4, poly[round], r[d-1-round]);
	 }

	 //now P "tells" V \tilde{A}(r) and \tilde{B^T}(r') and V checks final message based on this
	 //i.e. V checks g_{d-1}(r) = beta(z, p) \tilde{A}(r_{d-1}, ..., r1, r0) \tilde{B^T}(r_{d-1}, ..., r0)
	 //If so, V believes P as long as \tilde{A}(r) and \tilde{B^T}(r') are as claimed

	 rElt correct_out = myModMultR(betavals[0], myModMultR(V0[0], V1[0]));
	 if (!eqTest(correct_out, extrap_val))
	 {
	 	cout << "correct_out != extrap_val in check for final layer. correct_out is ";
	 	print_uintR(correct_out);
	 	cout << " and extrap_val is: ";
	 	print_uintR(extrap_val);
	 	cout << endl;
	 	//exit(1);
	 }

	 *ri0 = V0[0];
	 *ri1 = V1[0];
}


// Given V_i(z_i) = r_i reduces it to V_{i+1}(z_{i+1}) = r_{i+1}
// V is supposed to be list of vals at layer i+1, ri is r_i.
// d0 is log of number of sub-circuits
// d is log of number of gates in sub-circuit at layer i, ni is number of gates at layer i
// returns V(z_(i+1)). r: stores z_{i+1}, z: stores z_i.
uint128 sum_check_rouding_polygen(uint128* V, uint128 ri, int d0, int d, uint64 ni, uint128 alphaval, int* com_ct, int* rd_ct, uint128* r, uint128** poly, uint128* betavals, uint128* z, bool init, long lev){
	// initialize r & poly & betavals	// sample all randoms for sum-check
	for(int i = 0; i < d+d0; i++){
		r[i] = rand()%PRIME;
		if (r[i] < 4)
			r[i] = 4;
		r[i] = conv_to_mon(r[i], lev);
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = 0;
	}

	for (int i = 0; i < d; ++i)	// for final check (reducing to one pt)
		poly[d+d0][i] = 0;
	r[d+d0] = rand()%PRIME;
	if (r[d+d0] < d)
		r[d+d0] = d;
	r[d+d0] = conv_to_mon(r[d+d0], lev);

// NEEDS to be re calculated!!
	*com_ct = *com_ct+4*(d+d0)+2;
	*rd_ct = *rd_ct+d+d0-1;

	initialize_betavals(betavals, d+d0, z);
	uint64 num_terms = ni;
	uint128 tmp2, tmp3;
	uint64 hft, hhft;
	int qp, ones, q0, qp0, qp1;

	for(int round = 0; round < d0; round++){
		for(uint64 j = 0; j < num_terms; j++){
			qp = ((j>>d)<<(d-1));
			ones = (1<<(d-1))-1;
			q0 = (j>>(d-1))&1;
			qp0 = qp+(j&ones);
			qp1 = qp+ones;
			hft = (num_terms>>1);
			hhft = (hft>>1);

			if(j&hft){
				if (q0 == 0){
					poly[round][1] = myMod(poly[round][1] + myModMult(betavals[j], V[qp0]));
					tmp2 = myModMult(myMod(myMod(2*betavals[j]) + PRIMES[lev] - betavals[j - hft]), myMod(myMod(2*V[qp0]) + PRIMES[lev] - V[qp0-hhft]));
					tmp3 = myModMult(myMod(myModMult(CST[3][lev], betavals[j]) + myMod(2*(PRIMES[lev]-betavals[j - hft]))), myMod(myModMult(CST[3][lev],V[qp0]) + myMod(2*(PRIMES[lev]-V[qp0-hhft]))));
				}
				else{
					poly[round][1] = myMod(poly[round][1] + myModMult(betavals[j], myModMult(V[qp0], V[qp1])));
					tmp2 = myModMult(myMod(myMod(2*betavals[j]) + PRIMES[lev] - betavals[j - hft]), myModMult(myMod(myMod(2*V[qp0]) + PRIMES[lev] - V[qp0-hhft]), myMod(myMod(2*V[qp1]) + PRIMES[lev] - V[qp1-hhft])));
					tmp3 = myModMult(myMod(myModMult(CST[3][lev],betavals[j]) + myMod(2*(PRIMES[lev]-betavals[j - hft]))), myModMult(myMod(myModMult(CST[3][lev],V[qp0]) + myMod(2*(PRIMES[lev]-V[qp0-hhft]))), myMod(myModMult(CST[3][lev],V[qp1]) + myMod(2*(PRIMES[lev]-V[qp1-hhft])))));
				}
				poly[round][2] = myMod(poly[round][2] + tmp2);
				poly[round][3] = myMod(poly[round][3] + tmp3);
			}
			else{
				poly[round][0] = myMod(poly[round][0] + myModMult(betavals[j], myModMult(V[qp0], CST[1-q0][lev]+q0*V[qp1])));
			}
		}

		num_terms = num_terms >> 1;
		update_betavals(betavals, num_terms, r[d+d0-1-round]);
		updateV(V, num_terms >> 1, r[d+d0-1-round]);
	}

	uint128 Vconst = V[ones];
	for(int j = 0; j < num_terms; j++){
		hft = (num_terms>>1);
		if(j & hft){
			poly[d0][1] = myMod(poly[d0][1] + myModMult(betavals[j], myModMult(V[j-hft], Vconst)));
		}
		else{
			poly[d0][0] = myMod(poly[d0][0] + myModMult(betavals[j], V[j]));
			poly[d0][2] = myMod(poly[d0][2] + myModMult(myMod(myMod(2*betavals[j+hft]) + PRIMES[lev] - betavals[j]), myModMult(V[j], myMod(myMod(2*Vconst)+PRIMES[lev]-CST[1][lev]))));
		}
	}
	num_terms = num_terms >> 1;
	update_betavals(betavals, num_terms, r[d-1]);

//// gen poly for later check (reducing to one point)
	if (d != 1){
		poly[d+d0][0] = Vconst;
		poly[d+d0][1] = evaluate_V_i(d-1, num_terms, V, r);
		uint128* s = new uint128[d-1]();
		for (int i = 2; i < d; ++i){
			for (int j = 0; j < d-1; ++j)
				s[j] = myMod(CST[1][lev] + myModMult(myMod(r[j]+PRIMES[lev]-CST[1][lev]), CST[i][lev]));

			poly[d+d0][i] = evaluate_V_i(d-1, num_terms, V, s);
		}
	}

	uint128 cnt = myMod(myMod(CST[1][lev] + PRIMES[lev] - r[d-1]) + myModMult(r[d-1], Vconst));
	for(int round = d0+1; round < d0+d; round++){
		for(int j = 0; j < num_terms; j++){
			hft = (num_terms >> 1);
			if(j & hft){
				poly[round][1] = myMod(poly[round][1] + myModMult(betavals[j], myModMult(V[j], cnt)));
				poly[round][2] = myMod(poly[round][2] + myModMult(myMod(myMod(2*betavals[j]) + PRIMES[lev]-betavals[j-hft]), myModMult(myMod(myMod(2*V[j]) + PRIMES[lev]-V[j-hft]), cnt)));
			}
			else{
				poly[round][0] = myMod(poly[round][0] + myModMult(betavals[j], myModMult(V[j], cnt)));
			}
		}
		num_terms = num_terms >> 1;
		update_betavals(betavals, num_terms, r[d+d0-1-round]);
		updateV(V, num_terms, r[d+d0-1-round]);
	}

//// Verifier's check
	if((init) && ((myModMult(myMod(poly[0][0]+poly[0][1]), alphaval) != ri))){
		cout << "first check failed when ni was " << ni << endl;
		cout << "ri was ";print_uint(ri); cout << endl;
		cout << "poly[0][0] was ";print_uint(poly[0][0]);
		cout << " and poly[0][1] was ";print_uint(poly[0][1]);
		cout << " and their sum was ";print_uint(myMod(poly[0][0] + poly[0][1])); cout << endl;
		cout << " sum multiplied by alpha was "; print_uint(myModMult(myMod(poly[0][0] + poly[0][1]), alphaval)); cout << endl;
//		exit(1);
	}
	if((!init) && ((myMod(poly[0][0]+poly[0][1]) != ri))){
		cout<<"in"<<endl;
		print_ver(0, ni, poly, ri);
	}


	uint128 extrap_val = extrap(4, poly[0], r[d+d0-1]);
	for(int round = 1; round < d+d0; round++){
		if(myMod(poly[round][0] + poly[round][1]) != extrap_val)
			print_ver(round, ni, poly, extrap_val);

		if (round < d0)
			extrap_val = extrap(4, poly[round], r[d+d0-1-round]);
		else
			extrap_val = extrap(3, poly[round], r[d+d0-1-round]);
	}


//// Check "reducing to one point" (when d=1, we don't need it)

	if(d==1){
		uint128 correct_out = myModMult(betavals[0], myModMult(V[0], myMod(CST[1][lev]+myMod(PRIMES[lev]-r[0] + myModMult(r[0], V[0])))));
		if (correct_out != extrap_val){
			cout << "correct_out != extrap_val. correct_out is "; print_uint(correct_out);
			cout << " and extrap_val is: "; print_uint(extrap_val); cout << endl;
//			exit(1);
		}

		for (int i = 0; i < d0; ++i)
			r[i] = r[i+1];

		return V[0];
	}
	else{
		uint128 correct_out = myModMult(betavals[0], myModMult(poly[d+d0][1], myMod(CST[1][lev]+myMod(PRIMES[lev]-r[d-1]+ myModMult(r[d-1], poly[d+d0][0])))));
		 if(correct_out != extrap_val){
			cout << "correct_out != extrap_val. correct_out is "; print_uint(correct_out);
			cout << " and extrap_val is: "; print_uint(extrap_val); cout << endl;
//			exit(1);
		 }

		 for (int i = 0; i < d-1; ++i)
			 r[i] = myMod(CST[1][lev] + myModMult(myMod(r[i]+PRIMES[lev]-CST[1][lev]), r[d+d0]));
		 for (int i = d-1; i < d+d0-1; ++i)
			 r[i] = r[i+1];

		 return extrap(d, poly[d+d0], r[d+d0]);		// final result after sum-check
	}
}

// Given V_i(z_i) = r_i reduces it to V_{i+1}(z_{i+1}) = r_{i+1}
// V is supposed to be list of vals at layer i+1, ri is r_i.
// d0 is log of number of sub-circuits, d is log of number of gates in sub-circuit at layer i
// returns V(z_(i+1)). r: stores z_{i+1}, z: stores z_i.
rElt sum_check_rouding_polygenR(rElt* V, rElt ri, int d0, int d, clock_t* vtime_more, int* com_ct, int* rd_ct, rElt* r, rElt** poly, rElt* betavals, rElt* z, long lev = LV){
	for(int i = 0; i < d+d0-1; ++i){
		r[i] = conv_to_monR(rand_128R(), lev);
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = ZERO;
	}
	for (int i = 0; i < d; ++i)
		poly[d0][i] = ZERO;

	*com_ct = *com_ct+5*d0+d+2;
	*rd_ct = *rd_ct+d0+1;

	clock_t st = clock();
	evaluate_beta_fast(d0, z + d, r + d + d0-2, lev);
	*vtime_more += (clock()-st);

	initialize_betavalsR(betavals, d0, &(z[d]));
	int tot_terms = (1 << (d0+d-1));

	rElt* Vcopy1 = new rElt[tot_terms]();
	rElt* Vcopy2 = new rElt[tot_terms]();
	for (long i = 0; i < tot_terms; ++i){
		Vcopy1[i] = V[i];
		Vcopy2[i] = V[i];
	}

	for (long i = d-2; i >= 0; --i){
		tot_terms >>= 1;
		updateVRmid(Vcopy1, tot_terms, z[i], i);
		updateVRmid(Vcopy2, tot_terms, CSTR[1][lev], i);
	}

	int num_terms = (1 << d0);
	rElt tmp2, tmp3;
	rElt p0 = z[d-1];
	for(int round = 0; round < d0; round++){
		int hft = num_terms >> 1;
		for(int j = 0; j < num_terms; j++){
			if(j&hft){
				poly[round][1] = addR(poly[round][1], myModMultR(myModMultR(betavals[j], Vcopy1[j]), subR(addC(myModMultR(p0, Vcopy2[j]), CST[1][LV]), p0)));
				tmp2 = myModMultR(myModMultR(subR(mulC(betavals[j], CST[2][LV]), betavals[j-hft]), subR(mulC(Vcopy1[j], CST[2][LV]), Vcopy1[j-hft])), subR(addC(myModMultR(p0, subR(mulC(Vcopy2[j], CST[2][LV]), Vcopy2[j-hft])), CST[1][LV]), p0));
				tmp3 = myModMultR(myModMultR(subR(mulC(betavals[j], CST[3][LV]), mulC(betavals[j-hft], CST[2][LV])), subR(mulC(Vcopy1[j], CST[3][LV]), mulC(Vcopy1[j-hft], CST[2][LV]))), subR(addC(myModMultR(p0, subR(mulC(Vcopy2[j], CST[3][LV]), mulC(Vcopy2[j-hft], CST[2][LV]))), CST[1][LV]), p0));
				poly[round][2] = addR(poly[round][2], tmp2);
				poly[round][3] = addR(poly[round][3], tmp3);
			}
			else
				poly[round][0] = addR(poly[round][0], myModMultR(myModMultR(betavals[j], Vcopy1[j]), subR(addC(myModMultR(p0, Vcopy2[j]), CST[1][LV]), p0)));
		}

		num_terms = num_terms >> 1;
		update_betavalsR(betavals, num_terms, r[d+d0-2-round]);
		updateVR(Vcopy1, num_terms, r[d+d0-2-round]);
		updateVR(Vcopy2, num_terms, r[d+d0-2-round]);
		updateVR(V, num_terms*(1<<(d-1)), r[d+d0-2-round]);
	}


//// gen poly for later check (reducing to one point)
	poly[d0][1] = Vcopy1[0];
	poly[d0][0] = Vcopy2[0];

	rElt* pts = new rElt[d-1]();
	for (int i = 2; i < d; ++i){
		for (int j = 0; j < d-1; ++j)
			pts[j] = addC(mulC(addC(z[j], PRIMES[lev]-CST[1][lev]), CST[i][lev]), CST[1][lev]);
		poly[d0][i] = evaluate_V_iR(d-1, 1<<(d-1), V, pts);
	}


//// Verifier's check
	st = clock();
	if((!eqTest(addR(poly[0][0],poly[0][1]), ri))){
		cout << "first check failed when ni was " << (1<<(d+d0)) << endl;
		cout << "ri was ";print_uintR(ri); cout << endl;
		cout << "poly[0][0] was ";print_uintR(poly[0][0]);
		cout << " and poly[0][1] was ";print_uintR(poly[0][1]);
		cout << " and their sum was ";print_uintR(addR(poly[0][0], poly[0][1])); cout << endl;
		exit(1);
	}

	rElt extrap_val = extrapR(4, poly[0], r[d+d0-2]);
	for(int round = 1; round < d0; round++){
		if(!eqTest(addR(poly[round][0], poly[round][1]), extrap_val))
			print_verR(round, 1<<(d+d0), poly, extrap_val);
		extrap_val = extrapR(4, poly[round], r[d+d0-2-round]);
	}


//// Check "reducing to one point"

	rElt correct_out = myModMultR(myModMultR(betavals[0], poly[d0][1]), subR(addC(myModMultR(p0, poly[d0][0]), CST[1][LV]), p0));
	 if(!eqTest(correct_out, extrap_val)){
		cout << "correct_out != extrap_val. correct_out is "; print_uintR(correct_out);
		cout << " and extrap_val is: "; print_uintR(extrap_val); cout << endl;
	 }

	 rElt rtmp = r[d-2];
	 for (int i = 0; i < d-1; ++i)
		 r[i] = addC(myModMultR(addC(z[i], PRIMES[lev]-CST[1][lev]), rtmp), CST[1][lev]);


	 rElt rval = extrapR(d, poly[d0], rtmp);		// final result after sum-check
	 *vtime_more += (clock()-st);

	 return rval;	// final result after sum-check
}


// Given V_i(z_i) = r_i reduces it to V_{i+1}(z_{i+1}) = r_{i+1}
// V is supposed to be list of vals at layer i+1, ri is r_i.
// d0 is log of number of sub-circuits, d is log of number of gates in sub-circuit at layer i
// dp is log of number of gates in sub-circuit at layer i+1.
// LDP is coeffs of low digit removal poly
// returns V(z_(i+1)). r: stores z_{i+1}, z: stores z_i.
rElt sum_check_rouding_alphaR(rElt* V, rElt ri, int d0, int d, int dp, int* com_ct, int* rd_ct, clock_t* vtime, clock_t* vtime_more, uint128* LDpoly, rElt* r, rElt** poly, rElt* betavals, rElt* z, long lev = LV){
	for(int i = dp; i < dp+d0; i++)
		r[i] = z[i-dp+d];
	for(int i = 0; i < dp; i++){
		r[i] = conv_to_monR(rand_128R(), lev);
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = ZERO;
	}

	*com_ct = *com_ct+4*dp;
	*rd_ct = *rd_ct+dp;

	long alpha_terms = (1 << (d+dp));
	int V_terms = (1 << (d0+dp));

	rElt* alpha = new rElt[alpha_terms]();
	for (long i = 0; i < alpha_terms; ++i)
		alpha[i] = embC(LDpoly[i]);

	clock_t vt0 = clock();
	for(int round = 0; round < d; round++){
		alpha_terms >>= 1;
		updateVR(alpha, alpha_terms, z[d-1-round]);
	}
	*vtime += (clock() - vt0);		// measures Verifier's time for evaluating alpha for verification
	for(int round = 0; round < d0; round++){
		V_terms >>= 1;
		updateVR(V, V_terms, z[d+d0-1-round]);
	}

	vt0 = clock();
	rElt alphaval = evaluate_V_iR(dp, alpha_terms, alpha, r); 	// used in the final check
	*vtime += (clock() - vt0);		// measure Verifier's time for evaluating alpha for verification

//// Sum Check
	int num_terms = (1<<dp);
	int hft;
	for(int round = 0; round < dp; round++){
		for(int i = 0; i < num_terms; i++){
			hft = (num_terms >> 1);
			if( i & hft){
				poly[round][1] = addR(poly[round][1], myModMultR(alpha[i], V[i]));
				poly[round][2] = addR(poly[round][2], myModMultR(subR(mulC(alpha[i], CST[2][lev]), alpha[i-hft]), subR(mulC(V[i], CST[2][lev]), V[i-hft])));
			}
			else
				poly[round][0] = addR(poly[round][0], myModMultR(alpha[i], V[i]));
		}
		num_terms = num_terms >> 1;
		updateVR(alpha, num_terms, r[dp-1-round]);
		updateVR(V, num_terms, r[dp-1-round]);
	}

//// Verification
	clock_t st = clock();
	if (!eqTest(addR(poly[0][0], poly[0][1]), ri)){
		cout << "first check in rounding_eval failed when ni was " << (1<<(d+d0)) << endl;
		cout << "ri was "; print_uintR(ri); cout << endl;
		cout << "poly[0][0] was "; print_uintR(poly[0][0]);
		cout << " and poly[0][1] was ";  print_uintR(poly[0][1]);
		cout << " and their sum was ";  print_uintR(addR(poly[0][0], poly[0][1])); cout << endl;
//		exit(1);
	}
	rElt extrap_val = extrapR(3, poly[0], r[dp-1]);

	for(int round = 1; round < dp; round++){
		if (!eqTest(addR(poly[round][0], poly[round][1]), extrap_val))
			print_verR(round, (1<<(d+d0)), poly, extrap_val);
		extrap_val = extrapR(3, poly[round], r[dp-1-round]);
	}

	if (!eqTest(myModMultR(alphaval, V[0]), extrap_val))
		cout << "final verification failed!"<<endl;

	*vtime_more += (clock()-st);

	delete [] alpha;

	return V[0];
}

// Given V_i(z_i) = r_i reduces it to V_{i+1}(z_{i+1}) = r_{i+1}
// V is supposed to be list of vals at layer i+1, ri is r_i.
// d0 is log of number of sub-circuits
// d is log of number of gates in sub-circuit at layer i
// returns V(z_(i+1)). r: stores z_{i+1}, z: stores z_i.
rElt sum_check_rouding_unifyR(rElt* V, rElt ri, int d0, int d, clock_t* vtime_more, int* com_ct, int* rd_ct, rElt* r, rElt** poly, rElt* betavals, rElt* z, long lev = LV){
	for(int i = 0; i < d+d0+1; ++i){
		r[i] = conv_to_monR(rand_128R(), lev);
		poly[i][0] = poly[i][1] = poly[i][2] = poly[i][3] = ZERO;
	}

	for (int i = 0; i < d+2; ++i)
		poly[d0+1][i] = ZERO;

	*com_ct = *com_ct+5*d0+3+d+2;
	*rd_ct = *rd_ct+d0+1+d;

	clock_t st = clock();
	evaluate_beta_fast(d0, z + d, r + d + d0, lev);
	*vtime_more += (clock()-st);

	initialize_betavalsR(betavals, d0, &(z[d]));
	uint64 num_terms = (1 << d0);
	uint128 tot_terms = (1 << (d0+d+1));
	rElt tmp2, tmp3;

	rElt* Vcopy10 = new rElt[tot_terms]();
	rElt* Vcopy11 = new rElt[num_terms<<1]();
	rElt* Vcopy2 = new rElt[tot_terms]();
	for (long i = 0; i < tot_terms; ++i){
		Vcopy10[i] = V[i];
		Vcopy2[i] = V[i];
	}

	for (long i = d; i > 0; --i){
		tot_terms >>= 1;
		updateVRmid(Vcopy10, tot_terms, z[i-1], i);
		updateVRmid(Vcopy2, tot_terms, CSTR[1][lev], i);
	}

	for (long i = 0; i < (num_terms<<1); ++i){
		Vcopy11[i] = Vcopy10[i];
	}

	tot_terms >>= 1;
	updateVRmid(Vcopy10, tot_terms, CSTR[0][lev], 0);
	updateVRmid(Vcopy11, tot_terms, CSTR[1][lev], 0);
	updateVRmid(Vcopy2, tot_terms, CSTR[1][lev], 0);


	for(int round = 0; round < d0; round++){
		uint64 hft = num_terms >> 1;
		for(uint64 j = 0; j < num_terms; j++){
			if(j&hft){
				// cout <<j<<": "; print_uintR(Vcopy10[j]);
				poly[round][1] = addR(poly[round][1], myModMultR(betavals[j], addR(myModMultR(Vcopy11[j], Vcopy2[j]), Vcopy10[j])));
				tmp2 = myModMultR(subR(mulC(betavals[j], CST[2][LV]), betavals[j-hft]), addR(myModMultR(subR(mulC(Vcopy11[j], CST[2][LV]), Vcopy11[j-hft]), subR(mulC(Vcopy2[j], CST[2][LV]), Vcopy2[j-hft])), subR(mulC(Vcopy10[j], CST[2][LV]), Vcopy10[j-hft])));
				tmp3 = myModMultR(subR(mulC(betavals[j], CST[3][LV]), mulC(betavals[j-hft], CST[2][LV])), addR(myModMultR(subR(mulC(Vcopy11[j], CST[3][LV]), mulC(Vcopy11[j-hft], CST[2][LV])), subR(mulC(Vcopy2[j], CST[3][LV]), mulC(Vcopy2[j-hft], CST[2][LV]))), subR(mulC(Vcopy10[j], CST[3][LV]), mulC(Vcopy10[j-hft], CST[2][LV]))));
				poly[round][2] = addR(poly[round][2], tmp2);
				poly[round][3] = addR(poly[round][3], tmp3);
			}
			else
				poly[round][0] = addR(poly[round][0], myModMultR(betavals[j], addR(myModMultR(Vcopy11[j], Vcopy2[j]), Vcopy10[j])));
		}

		num_terms = num_terms >> 1;
		update_betavalsR(betavals, num_terms, r[d+d0-round]);
		updateVR(Vcopy10, num_terms, r[d+d0-round]);
		updateVR(Vcopy11, num_terms, r[d+d0-round]);
		updateVR(Vcopy2, num_terms, r[d+d0-round]);
		updateVR(V, num_terms*(1<<(d+1)), r[d+d0-round]);
	}


//// gen poly for later check (reducing to one point)
	poly[d0][0] = Vcopy10[0];
	poly[d0][1] = Vcopy11[0];

	poly[d0+1][0] = Vcopy2[0];
	poly[d0+1][1] = extrapR(2, poly[d0], r[d]);

	rElt* pts = new rElt[d+1]();
	for (int i = 2; i < d+2; ++i){
		pts[0] = addC(mulC(addC(r[d], PRIMES[lev]-CST[1][lev]), CST[i][lev]), CST[1][lev]);
		for (int j = 1; j < d+1; ++j)
			pts[j] = addC(mulC(addC(z[j-1], PRIMES[lev]-CST[1][lev]), CST[i][lev]), CST[1][lev]);
		poly[d0+1][i] = evaluate_V_iR(d+1, 1<<(d+1), V, pts);
	}


//// Verifier's check
	st = clock();
	if((!eqTest(addR(poly[0][0],poly[0][1]), ri))){
		cout << "first check failed when ni was " << (1<<(d+d0)) << endl;
		cout << "ri was ";print_uintR(ri); cout << endl;
		cout << "poly[0][0] was ";print_uintR(poly[0][0]);
		cout << " and poly[0][1] was ";print_uintR(poly[0][1]);
		cout << " and their sum was ";print_uintR(addR(poly[0][0], poly[0][1])); cout << endl;
//		exit(1);
	}

	rElt extrap_val = extrapR(4, poly[0], r[d+d0]);
	for(int round = 1; round < d0; round++){
		if(!eqTest(addR(poly[round][0], poly[round][1]), extrap_val))
			print_verR(round, 1<<(d+d0), poly, extrap_val);
		extrap_val = extrapR(4, poly[round], r[d+d0-round]);
	}


//// Check "reducing to one point"
//// we omitted the check: poly[d0+1][1] = extrapR(2, poly[d0], r[d])

	rElt correct_out = myModMultR(betavals[0], addR(myModMultR(poly[d0][1], poly[d0+1][0]), poly[d0][0]));
	 if(!eqTest(correct_out, extrap_val)){
		cout << "correct_out != extrap_val. correct_out is "; print_uintR(correct_out);
		cout << " and extrap_val is: "; print_uintR(extrap_val); cout << endl;
	 }

	 rElt rtmp = r[d-1];
	 r[0] = addC(myModMultR(addC(r[d], PRIMES[lev]-CST[1][lev]), rtmp), CST[1][lev]);
	 for (int i = d; i > 0; --i)
		 r[i] = addC(myModMultR(addC(z[i-1], PRIMES[lev]-CST[1][lev]), rtmp), CST[1][lev]);

	 rElt rval = extrapR(d+2, poly[d0+1], rtmp);		// final result after sum-check
	 *vtime_more += (clock()-st);

	 return rval;		// final result after sum-check
}


//V0 is supposed to be list of vals of matrix A in row-major order, V1 vals of matrix B, d is log of number of gates at layer i,
//ni is number of gates at layer i
rElt sum_check_gR(rElt* V0, rElt* V1, rElt ri, int threed, int ni, int* com_ct, int* rd_ct, rElt*r, rElt** poly, rElt* z, long lev = LV)
{
	int d = threed/3;
	for(int i = 0; i < 2*d; i++)
	{
		r[d+i] = z[i];
	}
	for(int i = 0; i < d; i++)
	{
		r[i] = conv_to_monR(rand_128R(), lev);
	}

	for(int i = 0; i < d; i++)
	{
		poly[i][0] = ZERO;
		poly[i][1] = ZERO;
		poly[i][2] = ZERO;
		poly[i][3] = ZERO;
	}


	*com_ct = *com_ct+3*d+2;
	*rd_ct = *rd_ct+d+1;

	int num_terms = ni;

	for(int round = 0; round < d; round++)
	{
		updateVR(V0, num_terms >> 1, r[3*d-1-round]);
		num_terms = num_terms >> 1;
	}

	num_terms = ni;
	for(int round = d; round < 2*d; round++)
	{
		updateVR(V1, num_terms >> 1, r[3*d-1-round]);
		num_terms = num_terms >> 1;
	}

	rElt temp1; rElt temp0; rElt cross;
	for(int round = 0; round < d; round++)
	{
		for(int i = 0; i < (num_terms >> 1); i++)
		{
			temp0 = myModMultR(V0[i], V1[i]);
			temp1 = myModMultR(V0[i + (num_terms>>1)], V1[i + (num_terms>>1)]);
			cross = myModMultR(subR(mulC(V0[i + (num_terms>>1)], CST[2][lev]), V0[i]), subR(mulC(V1[i + (num_terms>>1)], CST[2][lev]), V1[i]));

			poly[round][0] = addR(poly[round][0], temp0);
			poly[round][1] = addR(poly[round][1], temp1);
			poly[round][2] = addR(poly[round][2], cross);
		}
		updateVR(V0, num_terms >> 1, r[d-1-round]);
		updateVR(V1, num_terms >> 1, r[d-1-round]);
		num_terms = num_terms >> 1;
	}

	if (!eqTest(addR(poly[0][0], poly[0][1]), ri))
	{
		cout << "first check in onebintreesum failed when ni was " << ni << endl;
		cout << "ri was "; print_uintR(ri); cout << endl;
		cout << "poly[0][0] was "; print_uintR(poly[0][0]); cout << " and poly[0][1] was ";
		print_uintR(poly[0][1]); cout << " and their sum was ";
		print_uintR(addR(poly[0][0], poly[0][1])); cout << endl;
		exit(1);
	}
	rElt extrap_val = extrapR(3, poly[0], r[d-1]);
	for(int round = 1; round < d; round++)
	{
		if(!eqTest(addR(poly[round][0], poly[round][1]), extrap_val))
		{
			cout << "check for round " << round << " failed when ni was " << ni << "in onebintreecheck" <<  endl;
			cout << "extrap_val was "; print_uintR(extrap_val); cout << endl;
			cout << "poly[round][0] was "; print_uintR(poly[round][0]); cout << " and poly[round][1] was ";
			print_uintR(poly[round][1]); cout << " and their sum was "; print_uintR(addR(poly[round][0], poly[round][1])); cout << endl;
			exit(1);
	 	}
	 	extrap_val = extrapR(3, poly[round], r[d-1-round]);
	 }
	 return extrap_val;
}




void evaluate_circuit(circ* c, int size_mat, uint128*** coeff, long lev){
	clock_t t = clock();
	uint128 val1, val2;
	int di;
	int in1, in2;
	int type;

//// Evaluate matmul layers
	cout << "Matmul process..." <<endl;

	int n = size_mat;
	int matmul = c->num_levels-2;

	for(int i = 0; i < n; i++){
		for(int j = 0; j < n; j++){
			for(int k = 0; k < n; k++){
				c->gates[matmul][i*n+j] = myMod(c->gates[matmul][i*n+j] + myModMult(c->gates[matmul+1][i*n+k], c->gates[matmul+1][j*n+k+n*n]));
			}
		}
	}


//	for (int i = c->num_levels-2; i > c->num_levels-2-d_matmul; i--){
//		di = c->log_sublv_length[i];
//		for(int j = 0; j < c->sublv_length[i]*c->sublv_num[i]; ++j){
//			in1 = c->in1[i](j, di);
//			in2 = c->in2[i](j, di);
//			type = c->types[i](j, di);
//
//			val1=c->gates[i+1][in1];
//			val2=c->gates[i+1][in2];
//
//			if(type == 0)
//				c->gates[i][j]=myMod(val1+val2);
//			else if(type == 1)
//				c->gates[i][j]=myModMult(val1, val2);
//			else
//				cout <<"No type gate error!"<< endl;
//		}
//	}

	cout << "circuit eval (Matmul) is: " << ((double)clock()-t)/CLOCKS_PER_SEC <<" sec" << endl;

//// Evaluate rounding layers
// to see (before) rounding
	cout << "Rounding process..." <<endl;
	t = clock();
	int print_num = 16;
	int i = c->round_level_st+1;
	for(int j = 0; j < print_num; ++j){
		cout << j <<": ";
		print_uint(conv_from_mon(c->gates[i][j]));
		cout <<", ";
		if (j == print_num-1)
			cout << endl;
	}

	int depth = c->round_level_st;
	for (int round = 0; round < GAMMA; ++round){
//		cout<<"round:"<<round<<", log:"<<LOG_ep[E-round]+2<<endl;
		for (int sublv = 0; sublv < LOG_ep[E-round]+3; ++sublv){
			int i = depth - sublv;
			di = c->log_sublv_length[i];
			int ones =  (1 << (di+1)) - 1;

			for(int j = 0; j < c->sublv_length[i]*c->sublv_num[i]; ++j){
				in1 = c->in1[i](j, di);
				in2 = c->in2[i](j, di);
				type = c->types[i](j, di);
				val1 = c->gates[i+1][in1];
				val2 = c->gates[i+1][in2];

				if(type == 2){	// eval
					//c->gates[i][j] = simRounding(c->gates[11][j]);
					c->gates[i][j] = myMod(val1 + myModMult(val2, c->gates[i+1][((j >> di) << (di+1)) + ones]));
				}
				else if(type == 3){	// poly gen
					if ((j >> (di-1)) & 1)
						c->gates[i][j]= myModMult(val1, val2);
					else
						c->gates[i][j]= val1;
				}
				else if(type == 4){
					c->gates[i][j] = div_p(val1);
				}
				else if (type == 5){ // eval alpha
					in1 <<= LOG_sqr_ep[E-round];
					c->gates[i][j] = evalPolyVec(coeff[LV][j&((1<<di)-1)], c->gates[i+1], in1, (1<<LOG_sqr_ep[E-round]));
				}
				else if (type == 6){ // extract
					c->gates[i][j] = val1;
				}
				else{
					cout <<"No type gate error!"<<endl;
				}


// to see (after) rounding
				if ((c->types[i](j, di) == 4)&&(j<print_num)){
					cout << j <<": ";
					print_uint(conv_from_mon(c->gates[i][j], LV-1));
					cout <<", ";
					if (j == print_num-1)
						cout << endl;
				}
			}
		}
		depth -= (LOG_ep[E-round]+3);
		LV -= 1;
	}

	cout << endl;
	cout << "circuit eval (rounding) is: " << ((double)clock()-t)/CLOCKS_PER_SEC <<" sec" << endl;
}

int add0(int j, int d){
	return 0;
}

int mult1(int j, int d){
	return 1;
}

int eval2(int j, int d){
	return 2;
}

int round3(int j, int d){
	return 3;
}

int divp4(int j, int d_){
	return 4;
}

int eval5alpha(int j, int d){
	return 5;
}

int extract6(int j, int d){
	return 6;
}

int in1bintree(int j, int d){
	return (j << 1);
}

int in2bintree(int j, int d){
	return (j << 1) + 1;
}

//d is number of bits in gate label
int in1matmult(int p, int d){
	//p is (i, j, k), where i is of length d/3. want to return (0, i, k)
	int all_ones = myPow(2, d/3)-1;
	int i = (p >> (2*d/3)) & all_ones;
	int k = p & all_ones;
	return (i << d/3) + k;
}

//d is number of bits in gate label
int in2matmult(int p, int d)
{
    //all_ones is 2*d/3 1s
	int all_ones = myPow(2, 2*d/3)-1;
	//p is (i, j, k), where i is of length d/3. want to return (1, j, k)
	//j & all_ones is (0, k, j). adding all_ones+1 makes this (1, j, k)
	//cout << " and i am returning " << (p & all_ones) << " plus " << (all_ones + 1) << endl;
	return (p & all_ones) + (all_ones + 1);
}

/// let d be the log_num of gates for each rounding sub circuits
int in1rounding(int j, int d){
	uint128 low = (1 << (d-1)) - 1;
	uint128 high = (j >> d) << (d-1);
	return (high + (low & j));
}

int in2rounding(int j, int d){
	uint128 low = (1 << (d-1)) - 1;
	uint128 high = (j >> d) << (d-1);
	return high + low;
}

int in1eval_old(int j, int d){
	return (j << d);
}

int in2eval_old(int j, int d){
	return ((j+1) << d) - 1;
}

int in1eval(int j, int d){
	return (j << 1);
}

int in2eval(int j, int d){
	return (j << 1) + 1;
}


int in1divp(int j, int d){
	return j;
}

int in2divp(int j, int d){
	return j;
}

int in1evalalpha(int j, int d){
	return (j >> d);
}

int in2evalalpha(int j, int d){
	return (j >> d);
}



circ* construct_circ_init(int total_depth){
	circ* c = (circ*) malloc(sizeof(circ));
	c->sublv_length = (int*) calloc(total_depth+1, sizeof(int*));
	c->log_sublv_length = (int*) calloc(total_depth+1, sizeof(int*));
	c->sublv_num = (int*) calloc(total_depth+1, sizeof(int*));
	c->log_sublv_num = (int*) calloc(total_depth+1, sizeof(int*));
	c->in1 = (fptr*) calloc(total_depth+1, sizeof(fptr));
	c->in2 = (fptr*) calloc(total_depth+1, sizeof(fptr));
	c->types = (fptr*) calloc(total_depth+1, sizeof(fptr));
	c->gates = (uint128**) calloc(total_depth+1, sizeof(uint128*));
	c->num_levels=total_depth+1;
	c->testtype = (int*) calloc(total_depth+1, sizeof(int));

	return c;
}


//// level depth: Input layer, level 0: Output layer
void construct_rnd_circ(circ* c, int init_level, int log_inputs, bool initial){
	int n = myPow(2, log_inputs);
	int rnd_depth = 0;
	for (int i = 0; i < GAMMA; ++i)		// for rounding
		rnd_depth += (LOG_ep[E-i]+3);

/// rounding layers (each logp rounding requires logep + 3 depth)
	int depth = init_level-rnd_depth;
	for (int round = GAMMA; round > 0; --round){
		int sublv_len1 = 1;								// for initial division and eval layer
		int sublv_log1 = 0;
		int sublv_len2 = myPow(2, LOG_sqr_ep[E-round+1]);		// for polygen layer
		int sublv_log2 = LOG_sqr_ep[E-round+1];
		for (int sublv = 0; sublv < LOG_ep[E-round+1]+3; ++sublv){
			int i = sublv + depth;
			if (sublv == 0){										// divide-by-p layer
				c->sublv_length[i] = sublv_len1;
				c->log_sublv_length[i] = sublv_log1;
				c->sublv_num[i] = n;
				c->log_sublv_num[i] = log_inputs;
				c->gates[i] = (uint128*) calloc(c->sublv_length[i]*c->sublv_num[i], sizeof(uint128));
				c->in1[i] = in1divp;
				c->in2[i] = in2divp;
				c->types[i] = divp4;
				c->testtype[i] = c->types[i](0,0);
			}
			else if (sublv < LOG_rem[E-round+1]+3){
				c->sublv_length[i] = sublv_len1;
				c->log_sublv_length[i] = sublv_log1;
				c->sublv_num[i] = n;
				c->log_sublv_num[i] = log_inputs;
				c->gates[i] = (uint128*) calloc(c->sublv_length[i]*c->sublv_num[i], sizeof(uint128));
				if (sublv == LOG_rem[E-round+1]+2){				// eval layer
					c->in1[i] = in1evalalpha;
					c->in2[i] = in2evalalpha;
					c->types[i] = eval5alpha;
				}
				else if (sublv == 1){							// extract layer
					c->in1[i] = in1eval;
					c->in2[i] = in2eval;
					c->types[i] = extract6;
				}
				else{											// unify layer
					c->in1[i] = in1eval;
					c->in2[i] = in2eval;
					c->types[i] = eval2;
				}

				sublv_len1 <<= 1;
				sublv_log1++;
				c->testtype[i] = c->types[i](0,0);
			}
			else	{												// polygen layer
				c->sublv_length[i] = sublv_len2;
				c->log_sublv_length[i] = sublv_log2;
				c->sublv_num[i] = n;
				c->log_sublv_num[i] = log_inputs;
				c->gates[i] = (uint128*) calloc(c->sublv_length[i]*c->sublv_num[i], sizeof(uint128));
				c->in1[i] = in1rounding;
				c->in2[i] = in2rounding;
				c->types[i] = round3;
				c->testtype[i] = c->types[i](0,0);

				sublv_len2 >>= 1;
				sublv_log2--;
			}
		}
		depth += LOG_ep[E-round+1]+3;
	}

	if (initial == true){
	/// Input layer (total_depth)
		c->sublv_length[init_level] = n;
		c->log_sublv_length[init_level] = log_inputs;
		c->sublv_num[init_level] = 1;
		c->log_sublv_num[init_level] = 0;
		c->gates[init_level] = (uint128*) calloc(n, sizeof(uint128));
	 //shouldn't need in1, in2, or type for input level. shouldn't need the level_length stuff either I don't think
	}
}

void construct_matmul_circ(circ* c, int init_level, int log_size){
//// Matmul layers (total_depth to total_depth-(d+1))
	int n = myPow(2, log_size);
	int n_squared = n*n;
	int two_to_j = 1;
	for(int j = 0; j < log_size+1; ++j){
		int i = j + init_level-(log_size+1);
		c->sublv_length[i] = n_squared * two_to_j;
		c->log_sublv_length[i] = 2*log_size+j;
		c->sublv_num[i] = 1;
		c->log_sublv_num[i] = 0;
		c->gates[i] = (uint128*) calloc(c->sublv_length[i], sizeof(uint128));
		if(j < log_size){
			c->in1[i] = in1bintree;
			c->in2[i] = in2bintree;
			c->types[i] = add0;
		}
		else{
			c->in1[i] = in1matmult;
			c->in2[i] = in2matmult;
			c->types[i] = mult1;
		}
		two_to_j <<= 1;
		c->testtype[i] = c->types[i](0,0);
	}

//// Input layer (total_depth)
	c->sublv_length[init_level] = 2*n_squared;
	c->log_sublv_length[init_level] = 2*log_size+1;
	c->sublv_num[init_level] = 1;
	c->log_sublv_num[init_level] = 0;
	c->gates[init_level] = (uint128*) calloc(2*n_squared, sizeof(uint128));
////shouldn't need in1, in2, or type for input level. shouldn't need the level_length stuff either I don't think
}

//// level depth: Input layer, level 0: Output layer
circ* construct_mat_circ_old(int d){
	clock_t t = clock();
	int n = myPow(2, d);
	int n_squared = n*n;
	int gamma = 2; 						// (eta / logp)
	int total_depth;
	total_depth = d+1;					// for mat mul
	for (int i = 0; i < gamma; ++i)		// for rounding
		total_depth += (LOG_ep[E-i]+3);

	circ* c = (circ*) malloc(sizeof(circ));
	c->sublv_length = (int*) calloc(total_depth+1, sizeof(int*));
	c->log_sublv_length = (int*) calloc(total_depth+1, sizeof(int*));
	c->sublv_num = (int*) calloc(total_depth+1, sizeof(int*));
	c->log_sublv_num = (int*) calloc(total_depth+1, sizeof(int*));
	c->in1 = (fptr*) calloc(total_depth+1, sizeof(fptr));
	c->in2 = (fptr*) calloc(total_depth+1, sizeof(fptr));
	c->types = (fptr*) calloc(total_depth+1, sizeof(fptr));
	c->gates = (uint128**) calloc(total_depth+1, sizeof(uint128*));
	c->num_levels = total_depth+1;
	c->round_level_st = total_depth-(d+1)-1;
	c->testtype = (int*) calloc(total_depth+1, sizeof(int));

/// rounding layers (each logp rounding requires logep + 3 depth)
	int depth = 0;
	for (int round = gamma; round > 0; --round){
		int sublv_len1 = 1;								// for initial division and eval
		int sublv_log1 = 0;
		int sublv_len2 = myPow(2, LOG_sqr_ep[E-round+1]);	// for poly gen
		int sublv_log2 = LOG_sqr_ep[E-round+1];
		for (int sublv = 0; sublv < LOG_ep[E-round+1]+3; ++sublv){
			int i = sublv + depth;
			if (sublv == 0){										// initial division layer
				c->sublv_length[i] = sublv_len1;
				c->log_sublv_length[i] = sublv_log1;
				c->sublv_num[i] = n_squared;
				c->log_sublv_num[i] = 2*d;
				c->gates[i] = (uint128*) calloc(c->sublv_length[i]*c->sublv_num[i], sizeof(uint128));
				c->in1[i] = in1divp;
				c->in2[i] = in2divp;
				c->types[i] = divp4;
				c->testtype[i] = c->types[i](0,0);

//				cout << "sublv: "<<sublv<<", lvleng ,log: "<<c->sublv_length[i]*c->sublv_num[i] << ", "
//						<< c->log_sublv_length[i]+c->log_sublv_num[i]<<" type: "<< c->types[i](0,0)<<endl;
			}
			else if (sublv < LOG_rem[E-round+1]+3){				// rounding eval layer
				c->sublv_length[i] = sublv_len1;
				c->log_sublv_length[i] = sublv_log1;
				c->sublv_num[i] = n_squared;
				c->log_sublv_num[i] = 2*d;
				c->gates[i] = (uint128*) calloc(c->sublv_length[i]*c->sublv_num[i], sizeof(uint128));
				if (sublv == LOG_rem[E-round+1]+2){
					c->in1[i] = in1evalalpha;
					c->in2[i] = in2evalalpha;
					c->types[i] = eval5alpha;
				}
				else if (sublv == 1){
					c->in1[i] = in1eval;
					c->in2[i] = in2eval;
					c->types[i] = extract6;
				}
				else{
					c->in1[i] = in1eval;
					c->in2[i] = in2eval;
					c->types[i] = eval2;
				}
//				cout << "sublv: "<<sublv<<", lvleng ,log: "<<c->sublv_length[i]*c->sublv_num[i]<< ", "<<c->log_sublv_length[i]+c->log_sublv_num[i]<<" type: "<< c->types[i](0,0)<<endl;

				sublv_len1 <<= 1;
				sublv_log1++;
				c->testtype[i] = c->types[i](0,0);
			}
			else	{												// rounding poly gen layer
				c->sublv_length[i] = sublv_len2;
				c->log_sublv_length[i] = sublv_log2;
				c->sublv_num[i] = n_squared;
				c->log_sublv_num[i] = 2*d;
				c->gates[i] = (uint128*) calloc(c->sublv_length[i]*c->sublv_num[i], sizeof(uint128));
				c->in1[i] = in1rounding;
				c->in2[i] = in2rounding;
				c->types[i] = round3;
				c->testtype[i] = c->types[i](0,0);

//				cout << "sublv: "<<sublv<<", lvleng ,log: "<<c->sublv_length[i]*c->sublv_num[i]<< ", "<<c->log_sublv_length[i]+c->log_sublv_num[i]<<" type: "<< c->types[i](0,0)<<endl;

				sublv_len2 >>= 1;
				sublv_log2--;
			}
		}
		depth += LOG_ep[E-round+1]+3;
	}


/// Matmul layers (total_depth-(d+1) to total_depth-1)
	int two_to_j = 1;
	for(int j = 0; j < d+1; ++j){
		int i = j + total_depth-(d+1);
		c->sublv_length[i] = n_squared * two_to_j;
		c->log_sublv_length[i] = 2*d+j;
		c->sublv_num[i] = 1;
		c->log_sublv_num[i] = 0;
		c->gates[i] = (uint128*) calloc(c->sublv_length[i], sizeof(uint128));
		if(j < d){
			c->in1[i] = in1bintree;
			c->in2[i] = in2bintree;
			c->types[i] = add0;
		}
		else{
			c->in1[i] = in1matmult;
			c->in2[i] = in2matmult;
			c->types[i] = mult1;
		}
		two_to_j <<= 1;
		c->testtype[i] = c->types[i](0,0);
	}


/// Input layer (total_depth)
	c->sublv_length[total_depth] = 2*n_squared;
	c->log_sublv_length[total_depth] = 2*d+1;
	c->sublv_num[total_depth] = 1;
	c->log_sublv_num[total_depth] = 0;
	c->gates[total_depth] = (uint128*) calloc(2*n_squared, sizeof(uint128));
 //shouldn't need in1, in2, or type for input level. shouldn't need the level_length stuff either I don't think
	cout << "time to allocate memory in construction function is: " << (double) ((double)clock()-(double)t)/(double) CLOCKS_PER_SEC << endl;

	t = clock();
	for(int i = 0; i < 2*n_squared; i++){
		c->gates[total_depth][i] = conv_to_mon(rand()%PRIMES[E], E); //conv_to_mon(myModPE(rand_128(unif, &gen)), E);
		//c->gates[total_depth][i] = conv_to_mon(i & (myPow(2, 2*d)-1), E);
	}
	cout << "time to randomly generate data is: " << (double) ((double)clock()-(double)t)/(double) CLOCKS_PER_SEC << endl;

	return c;
}

//// level depth: Input layer, level 0: Output layer
void construct_mat_circ(circ* c, int init_layer, int log_dim, bool initial){
	int n = myPow(2, log_dim);
	int n_squared = n*n;
	int total_depth = log_dim + 1;					// for mat mul

/// Matmul layers (init_layer : input, init_layer - total_depth: output) (construct from output to input layer)
	int two_to_j = 1;
	for(int j = 0; j < total_depth; ++j){
		int i = init_layer - total_depth + j;
		c->sublv_length[i] = n_squared * two_to_j;
		c->log_sublv_length[i] = 2*log_dim+j;
		c->sublv_num[i] = 1;
		c->log_sublv_num[i] = 0;
		c->gates[i] = (uint128*) calloc(c->sublv_length[i], sizeof(uint128));
		if(j < log_dim){
			c->in1[i] = in1bintree;
			c->in2[i] = in2bintree;
			c->types[i] = add0;
		}
		else{
			c->in1[i] = in1matmult;
			c->in2[i] = in2matmult;
			c->types[i] = mult1;
		}
		two_to_j <<= 1;
		c->testtype[i] = c->types[i](0,0);
	}


	if (initial == true){
	/// Input layer (total_depth)
		c->sublv_length[init_layer] = 2*n_squared;
		c->log_sublv_length[init_layer] = 2*log_dim+1;
		c->sublv_num[init_layer] = 1;
		c->log_sublv_num[init_layer] = 0;
		c->gates[init_layer] = (uint128*) calloc(2*n_squared, sizeof(uint128));
	 //shouldn't need in1, in2, or type for input level. shouldn't need the level_length stuff either I don't think
	}
}


/// Generates (bit_input)*eta bit input at (layer_input).
void generate_input(circ* c, int num_input, int layer_input, int bit_input){
	int total_gates = c->sublv_length[layer_input] * c->sublv_num[layer_input];
	for(int i = 0; i < total_gates; i++){
		c->gates[layer_input][i] = conv_to_mon(rand_128(unif, &gen)%PRIMES[bit_input*GAMMA], E);			// generate random 2gamma p-digit (~ 2eta bit) integers
	}
}

void BasicTest(){
	clock_t sttt, endtt;

	uint128* a = new uint128[10000];
	uint128* b = new uint128[10000];
	uint128* ap = new uint128[10000];
	uint128* bp = new uint128[10000];


	long err = 0;
	for (long k = E; k > 0; --k){
		rElt* A = new rElt[10000];
		rElt* B = new rElt[10000];
		for (long i = 0; i < 10000; ++i){
			a[i] = rand_128(unif, &gen)%PRIMES[k-1];
			b[i] = rand_128(unif, &gen)%PRIMES[k-1];
			ap[i] = a[i]*PRIME;
//			if (a[i] % PRIME == 0)
//				a[i]++;
			ap[i] = conv_to_mon(ap[i], k);
			bp[i] = conv_to_mon(b[i], k);
			a[i] = conv_to_mon(a[i], k-1);
			b[i] = conv_to_mon(b[i], k-1);

//			A[i] = myModPER(rand_128R(unif, &gen));
//			B[i] = myModPER(rand_128R(unif, &gen));
//			for (int j = 0; j < DIM; ++j){
//				A[i].c[j] = A[i].c[j] % PRIMES[k];
//				B[i].c[j] = B[i].c[j] % PRIMES[k];
//			}
//			if ((A[i].c[0] == 0) && (A[i].c[1] == 0) && (A[i].c[2] == 0) && (A[i].c[3] == 0))
//				A[i].c[0]++;

//			A[i] = conv_to_monR(A[i], k);
//			B[i] = conv_to_monR(B[i], k);
//			B[i] = invR(A[i], k);
		}

		uint128* ab = new uint128[10000];
		rElt AB;

		sttt = clock();
		for (long i = 0; i < 10000; ++i){
//			ab = myMod(a[i], k);
////			ab = conv_from_mon(ab, k);
////			if (ab != 1)
////				err++;
			if (conv_from_mon(a[i], k-1) != conv_from_mon(ap[i]/PRIME, k-1)){
				cout << i << endl;
				print_uint(conv_from_mon(a[i], k-1)); cout << endl;
				print_uint(conv_from_mon(ap[i]/PRIME, k-1));
				exit(1);
			}


//			AB = addR(A[i], B[i], k);
//			AB = addR(A[i], B[i], k);
//			if (eqTest(AB, ZERO) != 1){
//				cout <<"AB:" <<endl;
//				print_uint(AB.c[0]); cout << endl;
//				print_uint(AB.c[1]); cout << endl;
//				print_uint(AB.c[2]); cout << endl;
//				print_uint(AB.c[3]); cout << endl;
//				err++;
//			}

		}
		endtt = clock();
		cout << "128: " <<((double) endtt - sttt) / 10000 << endl;
	}
	cout <<"err: "<< err << endl;
}

void LDPTest(){
	for (long j = 0; j < E-1; ++j){

		long st = PRIME;
		long e = E - j;
		long end = (e-1)*(PRIME-1)+1;
		uint128* LDpoly = new uint128[end]();
		genLowDigitPoly(e);
		LowDigitPolyIn(LDpoly, e);

		long err = 0;

		for (long i = 0; i < 10000; ++i){
			uint128 a = myModPE(rand_128(unif, &gen));
			for (long k = 0; k < j; ++k)
				a = div_p(a);
			uint128 b = evalPoly(LDpoly, a, end, e);

	//		cout <<"a: "; print_uint(a);
	//		cout << endl;
	//		cout <<"b: "; print_uint(b);
	//		cout << endl;
			if ((myMod(a + PRIMES[e]- b, e) > (PRIME-1)/2) && (myMod(b + PRIMES[e]- a, e) > (PRIME-1)/2))
				err++;
		}
		cout << e <<"th "<< err << "error occured!";
	}
}



/****************************************************************************************/
//									*MAIN*											  *
/****************************************************************************************/


int main(int argc, char** argv) {

	if((argc != 2)){
		cout << "argc!= 2. Command line arg should be log(n) for nxn matrix multiplication\n";
		exit(1);
	}

	srand(time(NULL));

	init_params();

//	BasicTest();
//	LDPTest();

	int maxLDdeg = (E-1)*(PRIME-1)+1;						// only for correctness check
	uint128** LDpoly = new uint128*[E+1]();
	cout << "Generating Lowest Digit Removal polynomial.." << endl;
	for (long i = 2; i < E+1; ++i){
//		genLowDigitPoly(i);								// comment out if once generated the file, and do not change PRIME and E from now on.
		LDpoly[i] = new uint128[1<<(LOG_ep[i]+1)]();
		LowDigitPolyIn(LDpoly[i], i);
		LDpoly[i][(1<<(LOG_ep[i]+1))-1] = 1;					// for later use in sum-check
	}
	cout << "Complete!" << endl;

////Test rounding and LDpoly
	uint128 input = myModPE(rand_128(unif, &gen));
	clock_t st, endt;
	st = clock();
	uint128 out1 = evalPoly(LDpoly[E], input, maxLDdeg, E);
	endt = clock();
	cout <<"eval. time: " << endt-st << endl;
	st = clock();
	uint128 out2 = simRounding(conv_to_mon(input, E), E);
	endt = clock();
	cout <<"rnd. time: " << endt-st << endl;
	cout << "input: "; print_uint(input); cout << endl;
	cout << "evalpoly: "; print_uint(out1); cout << endl;
	cout << "realRounding: "; print_uint(conv_from_mon(out2, E)); cout << endl;

	for (long i = 2; i < E+1; ++i){
		for (long j = 0; j < (1<<(LOG_ep[i]+1)); ++j)
			LDpoly[i][j] = conv_to_mon(LDpoly[i][j], i);
	}

	uint128*** partLDpoly = new uint128**[E+1]();
	for (long i = 2; i < E+1; ++i){
		partLDpoly[i] = new uint128*[1<<(LOG_rem[i]+1)]();
		int l = 0;
		for (long j = 0; j < (1<<(LOG_rem[i]+1)); ++j){
			partLDpoly[i][j] = new uint128[1<<LOG_sqr_ep[i]]();
			for (long k = 0; k < (1<<LOG_sqr_ep[i]); ++k){
				if (l < maxLDdeg)
					partLDpoly[i][j][k] = LDpoly[i][l];
				else
					partLDpoly[i][j][k] = 0;
				l++;
			}
		}
		partLDpoly[i][(1<<(LOG_rem[i]+1))-1][(1<<LOG_sqr_ep[i])-1] = CST[1][i];
	}


	int d = atoi(argv[1]);
	uint128 n = (1<<d);
	uint128 EP2 = (1<<LOG_ep[E]);							// smallest power of 2 larger than PRIME * E

	cout << endl;
	cout << "Matmul of 2^" << d <<" by "<< pow(2,d)<<" matrices start!"<<endl;
	cout << "PRIME: " << PRIME <<", E: "<< E << endl;
	cout << "eta: " << ETA <<", gamma: " << GAMMA << endl;
	cout << "L: " << (int) E/GAMMA - 1 << endl;


/********************************************
/Begin code to construct circuit of interest*
/********************************************/

	circ* c;
	int total_depth = 0;
	for (int i = 0; i < GAMMA; ++i)		// total_depth calculation (for rounding)
		total_depth += (LOG_ep[E-i]+3);
	total_depth += 1;

//// construct circuit
	clock_t t = clock();
	c = construct_circ_init(total_depth);
	c->round_level_st = total_depth-1-(1);
	// construct_matmul_circ(c, total_depth, d);
	c->sublv_length[total_depth] = 2*n*n;
	c->log_sublv_length[total_depth] = 1+2*d;
	c->sublv_num[total_depth] = 1;
	c->log_sublv_num[total_depth] = 0;
	c->gates[total_depth] = (uint128*) calloc(2*n*n, sizeof(uint128));

	construct_rnd_circ(c, total_depth - (1), 2*d, true);
	cout << "\n circuit construct time is: " << (double)((double) clock()-t)/CLOCKS_PER_SEC << endl;


//// generate input (at layer : total_depth)
	t = clock();
	generate_input(c, 2*myPow(2, d)*myPow(2, d), total_depth, 2);
	cout << "time to randomly generate data is: " << (double) ((double)clock()-(double)t)/(double) CLOCKS_PER_SEC << endl;


///// Test gates label
//	for (long i = c->num_levels-1; i >= 0; --i)
//		cout << i <<": "<< c->log_sublv_length[i] <<", "<< c->log_sublv_num[i] <<"type: " << c->testtype[i] << endl; //c->log_level_length[i]) << endl;


/************************************************************
/Begin code to evaluate circuit in verifiable manner*
/************************************************************/

/// Evaluate the circuit in Z_{p^e}
	evaluate_circuit(c, n, partLDpoly, E);

	long max_layer_size = n*n*EP2;
	long max_layer_log = 2*d+LOG_ep[E]+1;
	long max_poly_inter = max(d, 4)+3;

	rElt* Vcopy = (rElt*) malloc(max_layer_size*sizeof(rElt));		// for input, output V (for Verifier to check)
	rElt* z = (rElt*) calloc(max_layer_log, sizeof(rElt));			// stores z vector
	rElt* r = (rElt*) calloc(max_layer_log, sizeof(rElt));			// stores r vector
	rElt* betavals = (rElt*) calloc(max_layer_size, sizeof(rElt));	// stores max beta
	rElt** poly = (rElt**) malloc((max_layer_log+1) * sizeof(rElt*));		//stores poly for each round
	for(int i = 0; i < max_layer_log+1; i++)
		poly[i] = (rElt*) malloc(max_poly_inter*sizeof(rElt));
	for(int i = 0; i < 2*d; i++){
		z[i] = rand_128R();
		z[i] = conv_to_monR(z[i], LV);
	}


/// Embed the circuit values to Z_{p^e}[t]/(f(t)) for verification process
	rElt** gateVals = (rElt**) calloc(total_depth+1, sizeof(rElt*));
	for(int i = 0; i < total_depth+1; i++){
		gateVals[i] = (rElt*) malloc((c->sublv_num[i])*(c->sublv_length[i])*sizeof(rElt));
		for (long j = 0; j < (c->sublv_num[i])*(c->sublv_length[i]); ++j)
			gateVals[i][j] = embC(c->gates[i][j]);
		if (i == total_depth){
			for (long j = 0; j < (c->sublv_num[i])*(c->sublv_length[i]); ++j)
				Vcopy[j] = gateVals[i][j];
		}
	}


/// Verifier evaluates a random point in the MLE of the output   (0 layer)
	t=clock();
	rElt ri = evaluate_V_iR(2*d, n*n, gateVals[0], z, LV);
	clock_t v_time = clock() - t;
	clock_t v_time_more = 0;
	clock_t v_pretime = 0;

/// Start GKR protocol with Prover
	clock_t ct=0;
	clock_t pt=0;
	int com_ct=n*n; //counting the answer as communication here
	int rd_ct=1;
	rElt ri0=ZERO;
	rElt ri1=ZERO;
	rElt* temp;


//// Verification of rounding layer
	cout << "rounding ver start! "<< endl;
	t = clock();
	int depth = 0;
	for (int round = GAMMA; round > 0; --round){
		for (int sublv = 0; sublv < LOG_ep[E-round+1]+3; ++sublv){
			int i = sublv + depth;
			if (sublv == 0){										// initial division layer
				st = clock();
				for (int i = 0; i < DIM; ++i){
					ri.c[i]=ri.c[i]*PRIME;
				}
				LV++;
				for(int j = 0; j < 2*d; j++)
					z[j] = conv_to_monR(conv_from_monR(z[j], LV-1), LV);
				v_time_more += (clock()-st);
			}
			else if (sublv < LOG_rem[E-round+1]+3){				// rounding layer
				int log_sublv_len = c->log_sublv_length[i];
				int log_sublv_num = c->log_sublv_num[i];

				if (sublv == LOG_rem[E-round+1]+2){			// alpha eval layer
					ri=sum_check_rouding_alphaR(gateVals[i+1], ri, log_sublv_num, log_sublv_len, c->log_sublv_length[i+1], &com_ct, &rd_ct, &v_pretime, &v_time_more, LDpoly[LV], r, poly, betavals, z, LV);
					temp = z;
					z=r;
					r=temp;
				}
				else if (sublv == 1){						// extract layer
					st = clock();
					for(int j = 2*d; j > 0; --j)
						z[j] = z[j-1];
					z[0] = ZERO;
					v_time_more += (clock()-st);
				}
				else{										// unify layers
					ri=sum_check_rouding_unifyR(gateVals[i+1], ri, log_sublv_num, log_sublv_len, &v_time_more, &com_ct, &rd_ct, r, poly, betavals, z, LV);
					temp = z;
					z=r;
					r=temp;
				}
			}
			else	{												// polygen layers
				ri=sum_check_rouding_polygenR(gateVals[i+1], ri, c->log_sublv_num[i], c->log_sublv_length[i], &v_time_more, &com_ct, &rd_ct, r, poly, betavals, z, LV);
				temp = z;
				z=r;
				r=temp;
			}
		}
		depth += LOG_ep[E-round+1]+3;
	}

	cout << "rounding ver end!, takes " << (double) (clock()-t)/CLOCKS_PER_SEC << " sec" <<endl;


//// Verification of matmul layer
	cout << "Matmul ver start! "<< endl;
	t = clock();

	ri=sum_check_gR(gateVals[total_depth], gateVals[total_depth] + n*n, ri, 3*d, n*n, &com_ct, &rd_ct, r, poly, z, LV);

	cout << "Matmul ver end!, takes " << (double)((double) clock()-t)/CLOCKS_PER_SEC << endl;

	  //set the high order of values to be those of corresponding to index i, and the low order values of z to be those corresponding to index k
	for(int i = 0; i < d; i++)
		z[i] = r[i]; //set the low-order values of z
	for(int i = d; i < 2*d; i++)
		z[i] = r[d+i]; //set the low-order values of z

	t=clock();
	ri0 = evaluate_V_iR(2*d, n*n, Vcopy, z, E);

	  //set the high order of values to be those of corresponding to index j, and the low order values of z to be those corresponding to index k
	z=r;
	ri1 = evaluate_V_iR(2*d, n*n, &(Vcopy[n*n]), z, E);

	if(!eqTest(ri, myModMultR(ri0, ri1))){
		cout << "in very last check, ri != ri1. ri was : ";print_uintR(ri);
		cout << " and ri1 was ";print_uintR(myModMultR(ri0, ri1));
		cout << endl;
		//exit(1);
	}

	cout << "Vf online time is: " << (double)(v_time + (double) clock()-t)/CLOCKS_PER_SEC <<" sec"<< endl;
	cout << "Vf abbre time is: " << (double)(v_time_more)/CLOCKS_PER_SEC <<" sec" << endl;
	cout << "Vf precomp time is: " << (double) v_pretime/CLOCKS_PER_SEC <<" sec"<< endl;
	cout << "com_ct is: " << com_ct << " and rd_ct is: " << rd_ct << endl;

	return 0;
}
