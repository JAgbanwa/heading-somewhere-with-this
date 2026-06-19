// y^2 = (36n^3-19-12mn)^2 - (2m)^3 ; exhaustive in lo <= |m| <= hi, n unbounded.
// A = d+e, y = d-e, de = 2m^3. Divisor pairs (t,s) of 2m^3 generated in tandem
// (no division). Filter: A == 5 (mod 12). Segmented sieve factorization.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

typedef __int128 i128;
typedef unsigned __int128 u128;

#define WIN (1<<20)
#define MAXPF 12

static uint32_t *primes; static int nprimes;
static uint64_t rem_[WIN];
static uint32_t pf[WIN][MAXPF];
static uint8_t  pe[WIN][MAXPF];
static uint8_t  npf[WIN];

static FILE *out; static long raw_hits=0;

static void print_i128(i128 v, FILE *f){
    char buf[64]; int i=63; buf[i--]=0;
    int neg=v<0; u128 u=neg?(u128)(-v):(u128)v;
    if(u==0) buf[i--]='0';
    while(u){buf[i--]='0'+(int)(u%10);u/=10;}
    if(neg) buf[i--]='-';
    fputs(buf+i+1,f);
}
static inline int mod12_u128(u128 x){
    uint64_t hi=(uint64_t)(x>>64), lo=(uint64_t)x;
    return (int)(((hi%12)*4 + lo%12)%12);
}
static inline int is_root(int64_t n, int64_t m, i128 B){
    i128 nn=(i128)n;
    return (36*nn*nn*nn - (i128)12*m*nn - B)==0;
}
static void try_cubic(int64_t m, i128 A, i128 y){
    i128 B=A+19;
    double Bd=(double)B, md=(double)m;
    double cands[3]; int nc=0;
    double p=-md/3.0, q=-Bd/36.0;
    double disc=q*q/4.0+p*p*p/27.0;
    if(disc>=0){
        double sd=sqrt(disc);
        cands[nc++]=cbrt(-q/2.0+sd)+cbrt(-q/2.0-sd);
    } else {
        double r=2.0*sqrt(-p/3.0);
        double phi=acos(fmin(1.0,fmax(-1.0,(-q/2.0)/sqrt(-p*p*p/27.0))));
        cands[nc++]=r*cos(phi/3.0);
        cands[nc++]=r*cos((phi+2.0*M_PI)/3.0);
        cands[nc++]=r*cos((phi+4.0*M_PI)/3.0);
    }
    for(int i=0;i<nc;i++){
        double c=cands[i];
        if(fabs(c)>9.0e17) continue;
        int64_t base=(int64_t)llround(c);
        for(int64_t d=-2;d<=2;d++){
            int64_t n=base+d;
            if(is_root(n,m,B)){
                fprintf(out,"%lld %lld ",(long long)n,(long long)m);
                print_i128(y<0?-y:y,out); fputc('\n',out);
                fflush(out); raw_hits++;
            }
        }
    }
}

// divisor-pair recursion state; prime 2 is always the LAST level (bit shifts)
static int g_np; static uint32_t g_p[MAXPF+1]; static int g_E[MAXPF+1];
static u128 g_pw[MAXPF+1][110];
static int g_pw12[MAXPF+1][110];
static int g_E2;            // exponent of 2 in 2m^3
static int64_t g_m;
static int sh12[110];        // 2^e mod 12

static inline void leaf_pair(u128 t, u128 s, int t12, int s12){
    int r1=(t12+s12)%12, r2=(t12+12-s12)%12;
    if(((r1-5)&&(r1-7)&&(r2-5)&&(r2-7))) return;
    if(t>s) return;
    i128 ti=(i128)t, si=(i128)s;
    if(r1==5) try_cubic( g_m,  si+ti, si-ti);
    if(r1==7) try_cubic( g_m, -(si+ti), si-ti);
    if(r2==5) try_cubic(-g_m,  ti-si, ti+si);
    if(r2==7) try_cubic(-g_m,  si-ti, ti+si);
}

static void rec(int i, u128 t, u128 s, int t12, int s12){
    if(i==g_np){
        // innermost: powers of 2 via shifts
        int E2=g_E2;
        for(int e=0;e<=E2;e++)
            leaf_pair(t<<e, s<<(E2-e), (t12*sh12[e])%12, (s12*sh12[E2-e])%12);
        return;
    }
    int E=g_E[i];
    for(int e=0;e<=E;e++)
        rec(i+1, t*g_pw[i][e], s*g_pw[i][E-e], (t12*g_pw12[i][e])%12, (s12*g_pw12[i][E-e])%12);
}

int main(int argc,char**argv){
    int64_t lo=atoll(argv[1]), hi=atoll(argv[2]);
    out=fopen(argv[3],"w");
    sh12[0]=1; for(int e=1;e<110;e++) sh12[e]=(sh12[e-1]*2)%12;
    // primes up to sqrt(hi)
    uint32_t lim=(uint32_t)(sqrt((double)hi))+2;
    char *comp=calloc(lim+1,1);
    primes=malloc(12000*sizeof(uint32_t)); nprimes=0;
    for(uint32_t i=2;i<=lim;i++) if(!comp[i]){
        primes[nprimes++]=i;
        for(uint64_t j=(uint64_t)i*i;j<=lim;j+=i) comp[j]=1;
    }
    for(int64_t wlo=lo; wlo<=hi; wlo+=WIN){
        int64_t whi=wlo+WIN-1; if(whi>hi) whi=hi;
        int W=(int)(whi-wlo+1);
        for(int i=0;i<W;i++){ rem_[i]=(uint64_t)(wlo+i); npf[i]=0; }
        for(int k=0;k<nprimes;k++){
            uint32_t p=primes[k];
            if((uint64_t)p*p > (uint64_t)whi) break;
            int64_t start=((wlo+p-1)/p)*p;
            for(int64_t mlt=start; mlt<=whi; mlt+=p){
                int i=(int)(mlt-wlo);
                uint64_t r=rem_[i]; int e=0;
                while(r%p==0){ r/=p; e++; }
                if(e){ pf[i][npf[i]]=p; pe[i][npf[i]]=(uint8_t)e; npf[i]++; rem_[i]=r; }
            }
        }
        for(int i=0;i<W;i++){
            int64_t m=wlo+i; if(m<1) continue;
            g_m=m; g_np=0; g_E2=1;
            for(int j=0;j<npf[i];j++){
                if(pf[i][j]==2){ g_E2=3*pe[i][j]+1; continue; }
                g_p[g_np]=pf[i][j];
                g_E[g_np]=3*pe[i][j];
                g_np++;
            }
            if(rem_[i]>1){ g_p[g_np]=(uint32_t)rem_[i]; g_E[g_np]=3; g_np++; }
            long ndivs=g_E2+1;
            for(int j=0;j<g_np;j++) ndivs*=(g_E[j]+1);
            if(ndivs>2000000) continue;
            for(int j=0;j<g_np;j++){
                g_pw[j][0]=1; g_pw12[j][0]=1;
                for(int e=1;e<=g_E[j];e++){
                    g_pw[j][e]=g_pw[j][e-1]*g_p[j];
                    g_pw12[j][e]=(int)((g_pw12[j][e-1]*(g_p[j]%12))%12);
                }
            }
            rec(0,(u128)1,(u128)1,1,1);
        }
        if(((wlo-lo)/WIN)%64==63){ fprintf(stderr,"at m=%lld hits=%ld\n",(long long)whi,raw_hits); }
    }
    fclose(out);
    fprintf(stderr,"done [%lld,%lld] raw hits=%ld\n",(long long)lo,(long long)hi,raw_hits);
    return 0;
}
