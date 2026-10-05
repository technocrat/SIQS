const SMALL_PRIMES = [
  2,  3,  5,  7, 11, 13, 17, 19, 23, 29,
  31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97,101,103,107,109,113,
  127,131,137,139,149,151,157,163,167,173,
  179,181,191,193,197,199,211,223,227,229,
  233,239,241,251,257,263,269,271,277,281,
  283,293,307,311,313,317,331,337,347,349,
  353,359,367,373,379,383,389,397,401,409,
  419,421,431,433,439,443,449,457,461,463,
  467, 479, 487, 491, 499, 503, 509
]

# ----------------------------------------------------------------------------
# Prime sieves
# ----------------------------------------------------------------------------

function primes_less_than(n::UInt32)::Vector{UInt32}
    if n < 3 return UInt32[] end
    if n < 4 return UInt32[2] end
    if n < 6 return UInt32[2, 3] end
    correction = (n % 6 > 1) ? 1 : 0
    rem_dict = Dict(0 => n, 1 => n - 1, 2 => n + 4, 3 => n + 3, 4 => n + 2, 5 => n + 1)
    n_val = rem_dict[n % 6]
    sieve = trues(n_val ÷ 3)
    sieve[1] = false
    for i in 0:(isqrt(n_val) ÷ 3)
        if sieve[i + 1]
            k = (3 * i + 1) | 1
            start1 = (k * k) ÷ 3 + 1
            step1 = 2 * k
            for idx in start1:step1:length(sieve)
                sieve[idx] = false
            end
            start2 = (k * k + 4 * k - 2 * k * (i & 1)) ÷ 3 + 1
            for idx in start2:step1:length(sieve)
                sieve[idx] = false
            end
        end
    end
    result = UInt32[2, 3]
    for i in 2:(n_val ÷ 3 - correction)
        if sieve[i]
            push!(result, UInt32((3 * (i - 1) + 1) | 1))
        end
    end
    result
end

function primes_less_than(n::Int)::Vector{Int}
    """
    generate a list of primes less than an upper value
    uses BitArray for storage to lower memory footprint
    primes_less_than(10)  # [2, 3, 5, 7]
    :param n: return primes less than this value
    :return: array containing primes less than n
    """
    if n < 3 return Int[] end
    if n < 4 return [2] end
    if n < 6 return [2, 3] end
    correction = (n % 6 > 1) ? 1 : 0
    rem_dict = Dict(0 => n, 1 => n - 1, 2 => n + 4, 3 => n + 3, 4 => n + 2, 5 => n + 1)
    n_val = rem_dict[n % 6]
    sieve = trues(n_val ÷ 3)
    sieve[1] = false
    for i in 0:(isqrt(n_val) ÷ 3)
        if sieve[i + 1]
            k = (3 * i + 1) | 1
            start1 = (k * k) ÷ 3 + 1
            step1 = 2 * k
            for idx in start1:step1:length(sieve)
                sieve[idx] = false
            end
            start2 = (k * k + 4 * k - 2 * k * (i & 1)) ÷ 3 + 1
            for idx in start2:step1:length(sieve)
                sieve[idx] = false
            end
        end
    end
    result = [2, 3]
    for i in 2:(n_val ÷ 3 - correction)
        if sieve[i]
            push!(result, (3 * (i - 1) + 1) | 1)
        end
    end
    return result
end


# ----------------------------------------------------------------------------
# Random BigInt prime number with fixed size in digits
# ----------------------------------------------------------------------------

function randomprime(digits::Integer)::BigInt
    if digits <= 0
        error("randomdigits(digits), digits must be > 0")
    end
    local myprime
    while true
        lower = BigInt(10) ^ (digits - 1)
        upper = (BigInt(10) ^ digits) - 1
        n = rand(lower:upper)
        myprime = find_next_prime(n)
        if myprime <= upper
            break
        end
    end
    myprime
end

# ----------------------------------------------------------------------------
# Next BigInt prime 
# ----------------------------------------------------------------------------

function find_next_prime(n::BigInt)
  if n < 2
      return BigInt(2)
  end
  if n == 2
      return BigInt(3)
  end
  n = (n + 1) | 1  # first odd larger than n
  m = n % 6
  if m == 3
    if isprime(n + 2)
        return n + 2
    end
    n += 4
  elseif m == 5
    if isprime(n)
        return n
    end
    n += 2
  end
  m = n
  while true
    if isprime(m)
        return m
    end
    if isprime(m + 4)
        return m + 4
    end
    m += 6
  end
end

# ----------------------------------------------------------------------------
# Tests BigInt for primality using trial division, Miller_Rabin and Frobenius
# ----------------------------------------------------------------------------

function isprime(n::BigInt)
  if n < 2
      return false
  end
  for sp in SMALL_PRIMES
    if n % sp == 0
      return n in SMALL_PRIMES
    end
  end
  if !is_likely_prime_mr(n)
      return false
  end
  if n < 3_317_044_064_679_887_385_961_981
      return true
  end
  return isprime_frobenius(n)
end

# ----------------------------------------------------------------------------
# Tests BigInt for primality using Miller-Rabin test
# ----------------------------------------------------------------------------

function is_likely_prime_mr(n::BigInt, rounds::Integer = 14)
    """
    Test an BigInteger for primality using Miller-Rabin test.  This is a probalistic test.
    Increasing number of rounds (number of test bases) decreases probability of failure.
    Below are deterministic values for rounds. Function will set rounds to be deterministic if possible.
    :param n: BigInt to be tested
    :param rounds: Number of test rounds (number of bases to use)
    :return: True if likely prime, False otherwise
    """
    """
    rounds needed to be deterministic
    rounds  n < value
    1       2047
    2       1_373_653
    3       25_326_001
    4       3_215_031_751
    5       2_152_302_898_747
    6       3_474_749_660_383
    7       341_550_071_728_321
    8       does not improve on above
    9       3_825_123_056_546_413_051
    10,11   does not improve on above
    12      318_665_857_834_031_151_167_461
    13      3_317_044_064_679_887_385_961_981
    Smaller number of bases are needed if they are not required to be consecutive
    bases   n < value
    [31,73]    9_080_191
    [2, 7, 61] 4,294,967,296
    [2,13,23,1662803] 1_122_004_669_633
    [2, 325, 9375, 28178, 450775, 9780504, 1795265022]   18_446_744_073_709_551_616
    """
  if n < 2
      return false
  end
  if n < 3_317_044_064_679_887_385_961_981
    if n < 2_047
      rounds = 1
    elseif n < 9_080_191
      return is_likely_prime_mr_bases(n, [31, 73])
    elseif n < 4_294_967_296
      return is_likely_prime_mr_bases(n, [2, 7, 61])
    elseif n < 1_122_004_669_633
      return is_likely_prime_mr_bases(n, [2, 13, 23, 1662803])
    elseif n < 2_152_302_898_747
      rounds = 5
    elseif n < 3_474_749_660_383
      rounds = 6
    elseif n < 18_446_744_073_709_551_616
      return is_likely_prime_mr_bases(n, [2, 325, 9375, 28178, 450775, 9780504, 1795265022])
    elseif n < 318_665_857_834_031_151_167_461
      rounds = 12
    else
      rounds = 13
    end
  end
  rounds = max(rounds, 1)
  
  d = n - 1
  s = 0
  while iseven(d)
    d = div(d, 2)
    s += 1
  end
  pg = primegen()
  for i in 1:rounds
    a = take!(pg)
    if a >= n
        continue
    end
    x = powermod(a, d, n)
    if x == 1 || x == n - 1
        continue
    end
    composite = true
    for _ in 1:(s - 1)
      x = powermod(x, 2, n)
      if x == n - 1
        composite = false
        break
      end
      if x == 1
        return false
      end
    end
    if composite
        return false
    end
  end
  return true
end

# ----------------------------------------------------------------------------
# Tests Integer for primality using Miller-Rabin and specific bases
# ----------------------------------------------------------------------------

function is_likely_prime_mr_bases(n::Integer, bases = [2])
    """
    Test an Integer for primality using Miller-Rabin test.  This is a probalistic test.
    This version sets the bases to be used in the bases parameter.
    :param n: Integer to be tested
    :param bases: The specific bases to test with, default is [2]
    :return: True if likely prime, False otherwise
    """
  if n < 2
      return false
  end
  d = n - 1
  s = 0
  while iseven(d)
    d = div(d, 2)
    s += 1
  end
  for a in bases
    if a >= n
        continue
    end
    x = powermod(a, d, n)
    if x == 1 || x == n - 1
        continue
    end
    composite = true
    for _ in 1:(s - 1)
      x = powermod(x, 2, n)
      if x == n - 1
        composite = false
        break
      end
      if x == 1
        return false
      end
    end
    if composite
        return false
    end
  end
  return true
end

# ----------------------------------------------------------------------------
# Tests BigInteger for primality using Frobenius test
# ----------------------------------------------------------------------------

function isprime_frobenius(n::BigInt)
    x = BigInt(1) << div((ndigits(n, base=2) + 1), 2)
    while true
        delta = x * x - n
        if delta == 0
            return false
        end
        if delta < 0
            break
        end
        x -= 1 + div(delta, (2 * x))
    end
    if n % 4 == 3
        c = -1
    elseif n % 8 == 5
        c = 2
    elseif n % 24 == 17
        c = 3
    else
        c = 5
        while true
            jcn = jacobi(c, n)
            if jcn == 0
                return false
            end
            if jcn == -1
                break
            end
            c = c + 2
        end
    end
    a = (c < 3) ? 2 : 1
    b = 1
    a1 = 1
    b1 = 0
    a2 = a
    b2 = b
    k = n
    while k > 0
        if k % 2 == 1
            tb = mod((a1 * b2 + a2 * b1) , n)
            ta = mod((a1 * a2 + b1 * b2 * c) , n)
            a1 = ta
            b1 = tb
        end
        ta = mod((a2 * a2 + c * b2 * b2) , n)
        b2 = mod((2 * a2 * b2) , n)
        a2 = ta
        k >>= 1
    end
    (a1 == a) && (b1 == (n - b))
end

# ----------------------------------------------------------------------------
# Prime number generator
# ----------------------------------------------------------------------------

function primegen()
    Channel{Int}() do ch
        for n in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
            put!(ch, n)
        end
        r, sq, n = 7, 49, 49
        it = primegen()
        while take!(it) < r 
            continue
        end
        comp = Dict{Int, Int}()
        jump = (1, 6, 5, 4, 3, 2, 1, 4, 3, 2, 1, 2, 1, 4, 3,
                2, 1, 2, 1, 4, 3, 2, 1, 6, 5, 4, 3, 2, 1, 2)
        while true
            f = get(comp, n, 0)
            delete!(comp, n)
            if n == sq
                f, r = r, take!(it)
                sq = r * r
            elseif f == 0
                put!(ch, n)
            end
            if f != 0
                q = div(n, f)
                q += jump[(q % 30) + 1]
                while haskey(comp, q * f)
                    q += jump[(q % 30) + 1]
                end
                comp[q * f] = f
            end
            n += jump[(n % 30) + 1]
        end
    end
end
