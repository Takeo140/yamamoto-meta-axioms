__device__ __forceinline__
unsigned long long nonzeroMask(unsigned long long x) {
    // -x を 2 の補数で計算
    unsigned long long negx = (~x + 1ULL);
    return (negx | x) >> 63;
}

__device__ __forceinline__
unsigned long long branchlessSelect(unsigned long long control,
                                    unsigned long long a,
                                    unsigned long long b) {
    unsigned long long m = nonzeroMask(control);
    return a * m + b * (1ULL - m);
}
