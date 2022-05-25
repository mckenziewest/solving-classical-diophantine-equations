def teskeMinimizeAtJ(S, B, j, goth_p, N, primesPossiblyDividingGroupOrder):
    '''
    This is Teske's MINIMIZE algorithm.  See Teske's paper A SPACE EFFICIENT ALGORITHM FOR GROUP STRUCTURE COMPUTATION.
    INPUT:
    - ``S`` - a list of generators of the subgroup
    - ``B`` - a list of relations (lower triangular), the j-1 first of which are minimal
    - ``j`` - an integer between 0 and #S-1
    - ``goth_p`` - the place we're considering
    - ``N`` - the power of goth_p we are quotienting by
    - ``primesPossiblyDividingGroupOrder`` - any upper bound for the maximal prime divisor in phi(R) = phi(N).

    OUTPUT::
    B', same as B, except that the j'th relation is replaced by a j'th-minimal one.

    AUTHORS:
    Matchske (2018 ,https://github.com/bmatschke/solving-classical-diophantine-equations/blob/master/s-unit.sage)
    AKMRVW (2022)
    '''

    def findX(k,S,B,j, goth_p, N,x,c,gcdP0Bkk,p0,m):
        if k==-1:
            #check whether the x-vector is a relation:
            K = goth_p.number_field()
            StoX = 1
            for i in range(j+1):
                StoX = StoX * (K(S[i])**x[i])
            return (StoX - 1).valuation(goth_p) >= N

        else:
            if gcdP0Bkk[k]==0:
                print("Some error occured. Parameters k,S,j,R,x,c,gcdP0Bkk:",k,S,B,j, goth_p, n,x,c,gcdP0Bkk,p0,m)

            #try all possible values for x[k] and go deeper into the recursion:

            #m = [a for a in range(j)]
            #for i in range(j-1,k,-1):     #i=j-1...k+1
            #    m[i] = B[j,i] - p0*x[i]
            #    for n in range(i+1,j):
            #        m[i] = m[i] - m[n]*B[n][k]    # Important: I think here B[n][k] must be replaced by B[n][i]! (I think Teske's paper has a typo here.)
            #    m[i] = ZZ(m[i] / B[i][i])

            L = B[j][k]
            for i in range(k+1,j):
                L = L - m[i]*B[i][k]

            if not (L in ZZ):
                print ("Some error occured. Parameters p0,L,m,k,S,B,j,R,x,c,gcdP0Bkk:",k,S,B,j, goth_p, n,x,c,gcdP0Bkk,p0,m)

            if L%gcdP0Bkk[k] != 0:
                return False
            L = (L // gcdP0Bkk[k]) % B[k][k]
            Rt = B[k][k] // gcdP0Bkk[k]

            for rk in range(0,gcdP0Bkk[k]):
                x[k] = (L*c[k] + Rt*rk) % B[k][k];
                if not(x[k].is_integral()):
                    print("Error!")
                m[k] = B[j][k]-p0*x[k]
                for n in range(k+1,j):
                    m[k] = m[k] - m[n]*B[n][k]
                m[k] = m[k] // B[k][k]

                if findX(k-1,S,B,j, goth_p, N,x,c,gcdP0Bkk,p0,m):
                    return True

            return false

    #The following takes way too long for large primes in S:
    #P = []        #primes that may reduce b_{jj}
    #for i in prime_range(maxP+1):
    #    if B[j][j]%i == 0:
    #        P.append(i)

    #So let's do it quicker using more knowledge about the underlying group:
    P = [] #primes that may reduce b_{jj}
    for p in primesPossiblyDividingGroupOrder:
        if B[j][j]%p == 0:
            P.append(p)

    #print(S,j,primesPossiblyDividingGroupOrder, P)

    while True:
        #Reduce j'th relation by all previous ones:
        for k in range(j-1,-1,-1):             #k=j-1,...,0
            f = round(B[j][k]/B[k][k])
            if f != 0:
                for i in range(j+1):
                    B[j,i] = B[j][i] - f*B[k][i]

        if len(P) == 0:        #no primes left for reduction
            return B
        p0 = P[0]

        c = [a for a in range(j)]
        for k in range(j):
            c[k] = xgcd(p0,B[k][k])[1]    #a number ck such that gcd(p0,Bkk) = p*ck + Bkk*ak

        gcdP0Bkk = [a for a in range(j)]
        for k in range(j):
            gcdP0Bkk[k] = gcd(p0,B[k][k])

        x = [a for a in range(j+1)]
        x[j] = (B[j][j]//p0)

        if findX(j-1,S,B,j,goth_p,N,x,c,gcdP0Bkk,p0,[a for a in range(j)]):
            #smaller relation x has been found:
            for i in range(j+1):
                B[j,i] = x[i]
            if x[j]%p0 != 0:
                P.remove(p0)
        else:
            #reducing with respect to p0 is impossible:
            P.remove(p0)

    return B

def teskeMinimize(S, B, goth_p, n):
    '''
    Repeats the application of Teske's MINIMIZE algorithm along all relations of a set of generators.
    INPUT:
    - ``S`` - a list of generators of a subgroup of R
    - ``B`` - a list of |S| relations (lower triangular)
    - ``goth_p`` - place we're looking at
    - ``n`` - power of goth_p we're quotienting by
    OUTPUT:
    B', same as B, except that for each j, the j'th relation is replaced by a j'th-minimal one.
    '''
    B_copy = copy(B)

    q = int(goth_p.norm())
    prime_divisors = (q**min(1,n-1)*(q-1)).prime_divisors()
    for j in range(len(B.rows())):
        B_copy = teskeMinimizeAtJ(S, B_copy, j, goth_p, n,prime_divisors)
    return B_copy

def teske_diag(mu_vec, goth_p, n):
    r'''
    INPUT:
    - ``mu_vec`` - a vector of generators of the S-unit group that are coprime to ``goth_p``
    - ``goth_p`` - a place at which we're performing this task
    - ``n`` - the power of ``goth_p`` which we're quotienting the unit group by
    OUTPUT:
    a list of multiplicative orders of the elements of ``mu_vec`` when quotienting the set by ``goth_p**n``
    '''
    h = []
    for mui in mu_vec:
        h.append( unit_order_mod_prime_power(mui, goth_p, n))
    return h

def unit_order_mod_prime_power(curr_mu, gothp, n):
    # returns the mult. order of curr_mu inside OKSx \cap (1 + gothp^n) 
    old_d = 0
    K = curr_mu.parent()
    elt_to_test = K(1)
    q = gothp.norm()
    list_of_divs = divisors( q^(n-1)*(q-1) )
    for d in list_of_divs[:-1]:
        elt_to_test *= curr_mu^(d - old_d)
        eltshift1 = elt_to_test - 1
        if eltshift1.valuation(gothp) >= n:
            return d
        old_d = d
    return list_of_divs[-1]

## An example of using these items
# from sage.rings.number_field.S_unit_solver import mus, possible_mu0s
# K.<a> = NumberField(x^3 +4*x - 1)
# S = K.primes_above(110)
# OKSx = UnitGroup(K,S=tuple(S))
# goth_p = S[1]
# mu = [possible_mu0s(OKSx, S[1])[1]]+mus(OKSx, S[1])
# n = 6
# hvec = teske_diag(mu, goth_p, n)
# B = diagonal_matrix(hvec)
# new_B=teskeMinimize(mu, B, goth_p, n)
# new_mu = []
# for row in range(6):
#     myrel = prod(OKSx(mu[j])^new_B[row][j] for j in range(6))
#     new_mu.append(myrel)
# for j in range(6):
#     print( (new_mu[j]).exponents() )