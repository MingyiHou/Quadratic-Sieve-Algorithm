from random import randrange
import numpy as np
import math

#Trial Division 
def trialDivision(n,lst):
    #input:integer n, and a list of factor base
    #output: the corresponding exponent of the factor base
    expo_list=[]
    for i in range(len(lst)):
        count=0
        while n % lst[i]==0:
            count+=1
            n= n // lst[i]
        expo_list+=[count]

    return expo_list

#Get Factors of a number
def get_factors(n):
    #input: integer number you want to factorize
    #output: list of primes factors of n
    i=2 
    prime_factors=[]
    while i*i<=n:    # i<= sqrt(n) to save time
        if n%i:
            i+=1
        else:
            n//=i
            prime_factors+=[i]
    if n>1:
        prime_factors+=[n]
    #remove prime duplicates
    list_pf=list(set(prime_factors))
    return sorted(list_pf)

#Strong Pseudo-prime 
def strongPseudoprime(n):
    
    primes = [2,3,5,7,11]
    if n < 2: return False

    for p in primes:
        if n < p * p: return True
        if n % p == 0: return False
    r, s = 0, n - 1

    while s % 2 == 0:
        r += 1
        s //= 2
    k=3 #set 3 rounds of the test
    for _ in range(k):
        a = randrange(2, n - 1)
        x = pow(a, s, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def gcdd(a,b):
    a=abs(a)
    b=abs(b)
    count=0
    if a==0 or b==0:
        if (a>b):
            b=a
    else:
        while a%b!=0:
            count+=1
            a,b=b,a%b
    return b
# Use Extended Euclidean Algorithm-->inversemod 
def inversemod(m,n):
    m2=n
    olda,a =1,0
    oldb,b=0,1
    while n>0:
        q=m//n
        a,olda =olda-q*a,a
        b,oldb =oldb-q*b,b
        m,n=n,m%n

    return olda % m2

#Jacobi Part 
def Jacobi(a,n):
    a%=n
    result=1
    while a!=0:
        while a%2==0:
            a/=2
            n_mod_8=n%8
            if n_mod_8 in (3,5):
                result=-result
        a,n=n,a
        if a%4==3 and n%4==3:
            result=-result
        a%=n
    if n==1:
        return result
    else:
        return 0

def modexpo(a,b,m):
    n=1
    while b!=0:
        if b%2!=0:
            n=n*a%m
        b=b//2
        a=a*a%m
    return n 

def tonelli(a,p):
    def order2(n):
        s=0
        t=n
        while (t%2==0):
            t//=2
            s+=1
            return [s,t]

    def get_non_residue(p):
     for i in range(p):
        if (Jacobi(i,p)==-1):
            return i

    if Jacobi(a,p)!=1:
        #print('Not a square')
        return 0
    if p==2:
        return 1
    #compute p-1= 2^s *t 
    [s,t]=order2(p-1)
    #print("Computed {} =2^{} * {}".format(p-1,s,t))

    #find a non-residue b
    b=get_non_residue(p)
    inver_b=inversemod(b,p)

    #try to find i so (a/b^i)^t==1 mod p
    i_s=[0,2]
    #index i_s so i[j]=i_j 
    for k in range(2,s+1):
        check =modexpo(a*modexpo(inver_b,i_s[k-1],p),t*(2**(s-k)),p)
        if(check==1):
            i_s.append(i_s[k-1])
        else:
            i_s.append(i_s[k-1]+2**(k-1))
        #print("Options for the next i are {} and {}. {} works.".format(i_s[k-1],i_s[k-1]+2**(k-1),i_s[k]))
    
    mysqrt=modexpo(b,i_s[-1]/2,p) * modexpo(a*modexpo(inver_b,i_s[-1],p),(t+1)/2,p) %p
    #print("Thus, we get {}^2={} mod {}".format(mysqrt,a,p))
    return p-mysqrt


#Problem 4-Factor base
def factorBase(B,n):
    
    def plist(b):
        primelist=[]
        for i in range(2,b):
            if len(get_factors(i))==1 and i==get_factors(i)[0]:
                primelist+=[i]
        return primelist

    primelist=plist(B)  #get a list of primes less than given B
    factor_base=[] 
    #use for loop to extract a list of primes with Jacob(n/p)=1
    for p in primelist:
        if Jacobi(n,p)==1:
            factor_base+=[p]
    #print('Primes less than B and with Jacobi=1:')
    return factor_base

#Problem3-Row reduction: 

def rowreduction(M):
    first = 0
    nrows = len(M)
    ncols = len(M[0])

    for r in range(nrows):
        if first >= ncols:
            return M
        
        i = r
        while M[i][first] == 0:
            i += 1
            if i == nrows:
                i = r
                first += 1
                if ncols == first:
                    return M
        #swap rows
        M[i], M[r] = M[r], M[i]
        lv = M[r][first]
        M[r] = [(mrx // lv)%2 for mrx in M[r]]
        for i in range(nrows):
            if i != r:
                lv = M[i][first]
                M[i] = [(iv - lv * rv)%2 for rv, iv in zip(M[r], M[i])]
        first += 1
    return M
#returns the col list with pivots--'p' ,free variables--'free'
def get_pivoted_columns(M):
    M = rowreduction(M)
    pivotedlst = ['free'] * len(M[0])
    for rownum in range(len(M)):
        # if there exist a pivot in the rownum, give it 'p'
        if 1 in M[rownum]:
            pivotedlst[M[rownum].index(1)] = 'p'
    return pivotedlst

def find_solution(M):
    m = rowreduction(M)
    pivotlist = get_pivoted_columns(M)

    indexfree = []
    collect_solutions = []
    # make first free variable 1 and all other zero
    while 'free' in pivotlist:
        indexfree.append(pivotlist.index('free'))

        # make the previous false term==1 turn to 'checked'
        if 1 in pivotlist:
            pivotlist[pivotlist.index(1)] = 'checked'
        
        #set the chosen free variable to 1 
        pivotlist[indexfree[-1]] = 1

        # working on this list instead of the original pivotlist
        current_list = [i for i in pivotlist]

        for i in range(len(current_list)):
            # set all other free variables ==0
            if current_list[i] == 'free' or current_list[i] == 'checked':
                current_list[i] = 0

        for i in range(len(current_list)):
            if current_list[i] == 'p':
                for rownum in range(len(M)):
                    if m[rownum][i] == 1:
                        if m[rownum][indexfree[-1]] == 1:
                            current_list[i] = 1
                        else:
                            current_list[i] = 0
                        break

        collect_solutions.append(current_list)
    return  collect_solutions


#Problem 5-Sieve: 
def Sieve(n,B,M):
    fb =factorBase(B,n)
    r=[]   #list of r's
    h=[] #list of h(r)=log(r^2-n)
    t=[]   # t^2=q-1  factor bases

    print("\nFactor base of ", n, fb)
    for i in range(math.ceil(n**(1/2)),math.ceil(n**(1/2))+M):
        r+=[i]
        h+=[math.log(i**2-n)]

    for p in factorBase(B,n):
        lst=[]
        t.append(tonelli(n,p))
        print("Square root of {} (mod {}) is :{} ".format(n,p, tonelli(n,p)))
        for i in r:
            if (i**2-n)%p==0:
                lst+=[i]

    for i in range(len(r)):
        for j in range(len(fb)):
            if (r[i]**2-n)%fb[j]==0:
                h[i]-=math.log(fb[j])

    #looking for smooth values
    smooth=[]
    for i in range(len(r)):
        if -4< h[i]<4:
            smooth+=[r[i]]
    print("\nSmooth r and f(r):")
    for i in range(len(smooth)):
        print("r=",smooth[i], "f(r)= ",smooth[i]**2-n, "factors:",get_factors(smooth[i]**2-n))
    return smooth


#Problem 6
def QuadraticSieve(n, B, M):
    print("\nQuadratic Sieve of n={}, B={}, M={} ".format(n,B,M))
    print("\nPass the Strong Pseudoprime Test? ",strongPseudoprime(n))

    fb=factorBase(B,n)
    t=[]
    for p in fb:
        t+=[tonelli(n,p)]

    print("\nSolve for t^2=n mod p")
    sieve_r=Sieve(n,B,M)
    print('Smooth r list:\n',sieve_r)

    #Formed the matrix with factorizations in the columns.
    matrix=[]
    for r in sieve_r:
        r=(r**2-n)
        matrix+=[trialDivision(r,fb)]
    #Transpose the matrix
    matrixT=np.array(matrix).T.tolist()

    #Print each solution 
    solution=find_solution(matrixT)
    for i in range(len(solution)):
        print("\nSolution",i+1)
        print(solution[i])
    success=[]
    #Checking for solutions 
    for i in range(len(solution)):
        print("Checking for a factor using solution",i+1)
        product=1
        s=[]

        #product of corresponding r:
        for j in range(len(solution[0])):
            if solution[i][j]==1:
                product*=sieve_r[j]
                s.append(matrix[j])

        #sum pf exponent vectors
        expo=[0]*len(fb)
        sqrt=[0]*len(fb)
        
        for i in range(len(s)):
            for j in range(len(s[0])):
                expo[j]+=s[i][j]
                sqrt[j]=expo[j]//2
        
        prod=1
        for m in range(len(fb)):
            if sqrt[m]!=0:
                prod*=(fb[m]**sqrt[m])
        
        x=product%n
        y=prod%n
        
        print("Product of corresponding r is",product)
        print("Mod n that's x=",x)
        print("Sum of exponent vector is ",expo)
        print("Square root is",sqrt)
        print("Product is ",prod)
        print("Mod n that's y=", y)
        print("Sanity check:")
        print("x^2 mod n =", (x** 2) % n)
        print("y^2 mod n =", (y ** 2) % n)
                
        if gcdd(x-y,n)==1 or gcdd(x-y,n)==n:
            print("gcd(x-y,n)=", gcdd(x-y,n))
        else:
            success=success+[gcdd(x-y,n)]+[n//gcdd(x-y,n)]
            print("Success!",n,"=",gcdd(x-y,n),"*",n//gcdd(x-y,n))
            
    print("Finally, we get n's factors: ")
    return list(set(success))


print(QuadraticSieve(10378625636772128629,1000,64462))
