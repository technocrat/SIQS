# ----------------------------------------------------------------------------
# Nth root
# ----------------------------------------------------------------------------

function introot(n::BigInt, r=2)
    if n < 0
        if r % 2 == 0
            return nothing
        else
            return -introot(-n, r)
        end
    end
    if n < 2
        return n
    end
    if r == 2
        return isqrt(n)
    end
    lower, upper = 0, n
    while lower != (upper - 1)
        mid = div(lower + upper , 2)
        m = mid ^ r
        if m == n
            return mid
        elseif m < n
            lower = mid
        else
            upper = mid
        end
    end
    lower
end

# ----------------------------------------------------------------------------
# Is a power
# ----------------------------------------------------------------------------

function ispower(n::BigInt)
    # Returns the largest integer that, when squared/cubed/etc, yields n, or 0 if no such integer exists.
    # Note that the power to which this number is raised will be prime.
    for prime in primegen()
        r = introot(n, prime)
        if isnothing(r)
            continue
        end
        if r ^ prime == n
            return r
        end
        if r == 1
            return 0
        end
    end
end

# ----------------------------------------------------------------------------
# Jacobi symbol
# ----------------------------------------------------------------------------

function jacobi(n::Integer, k::Integer)
    rem(k, 2) != zero(k) || throw("Jacobi(n,k) k must be odd")

    n = mod(n, k)
    t = 1
    while n != zero(n)
        while rem(n, 2) == 0
            n = div(n, 2)
            r = k % 8
            if r == 3 || r == 5
                t = -t
            end
        end
        n, k = k, n
        if n % 4 == 3 && k % 4 == 3
            t = -t
        end
        n = mod(n, k)
    end
    if k == oneunit(k)
        return t
    else
        return 0
    end
end

# ----------------------------------------------------------------------------
# Legendre symbol
# ----------------------------------------------------------------------------

"""Legendre symbol `(n|p)` via Euler's criterion"""
function legendre(n::BigInt, p::UInt32)::Int32
    power = powermod(n, BigInt((p - UInt32(1)) ÷ UInt32(2)), BigInt(p))
    if power > 1
        return Int32(power - BigInt(p))   # == -1
    end
    return Int32(power)
end

# ----------------------------------------------------------------------------
# Tonelli–Shanks
# ----------------------------------------------------------------------------

"""Square roots of `a` mod `prime`; returns `(x, p - x)`"""
function tonelli_shanks(a::BigInt, prime::UInt32)::Tuple{UInt32,UInt32}
    p_u32 = prime
    p_big = BigInt(p_u32)

    a_mod = mod(a, p_big)
    pmod8 = p_u32 % UInt32(8)

    if pmod8 == UInt32(3) || pmod8 == UInt32(7)
        exponent = (p_u32 + UInt32(1)) ÷ UInt32(4)
        x = UInt32(powermod(a_mod, BigInt(exponent), p_big))
        return (x, p_u32 - x)
    end
    if pmod8 == UInt32(5)
        exponent = (p_u32 + UInt32(3)) ÷ UInt32(8)
        x = powermod(a_mod, BigInt(exponent), p_big)
        mult = BigInt(1)
        if mod(x * x, p_big) != a_mod
            exponent2 = (p_u32 - UInt32(1)) ÷ UInt32(4)
            mult = powermod(BigInt(2), BigInt(exponent2), p_big)
        end
        x = UInt32(mod(x * mult, p_big))
        return (x, p_u32 - x)
    end

    d = BigInt(2)
    symb = Int32(0)
    while symb != Int32(-1)
        symb = legendre(d, p_u32)
        d += 1
    end
    d -= 1
    nn = p_u32 - UInt32(1)
    s = UInt32(0)
    while nn % UInt32(2) == UInt32(0)
        nn >>= 1
        s += UInt32(1)
    end

    t = nn
    a_b = powermod(a_mod, BigInt(t), p_big)
    d_b = powermod(d, BigInt(t), p_big)

    m = BigInt(0)
    for i in UInt32(0):(s - UInt32(1))
        i1 = UInt32(2)^(s - UInt32(1) - i)
        i2 = powermod(d_b, m, p_big)
        i2 = mod(i2 * a_b, p_big)
        i3 = powermod(i2, BigInt(i1), p_big)
        if i3 == p_u32 - UInt32(1)
            m += BigInt(UInt32(2)^i)
        end
    end
    x_1 = powermod(a_mod, BigInt((t + UInt32(1)) ÷ UInt32(2)), p_big)
    x_2 = powermod(d_b, m ÷ BigInt(2), p_big)
    x = mod(x_1 * x_2, p_big)
    x = UInt32(x)
    return (x, p_u32 - x)
end

# ----------------------------------------------------------------------------
# Modular inverse
# ----------------------------------------------------------------------------

"""`x mod p` for a non-negative word-sized `p` without allocating (GMP `fdiv_ui`)"""
@inline function bmod(x::BigInt, p::Integer)::Int
    return Int(ccall((:__gmpz_fdiv_ui, Base.GMP.libgmp), Culong,
                     (Ref{BigInt}, Culong), x, p))
end

# reduce to a machine int first so no BigInt is created; `invmod` throws if
# the inverse does not exist
function modinv(n::BigInt, p::Int32)::Int32
    return Int32(invmod(bmod(n, p), Int(p)))
end

# ----------------------------------------------------------------------------
# Random BigInt with fixed size in digits
# ----------------------------------------------------------------------------

function randomdigits(digits::Integer)::BigInt
    if digits <= 0
        error("randomdigits(digits), digits must be > 0")
    end
    rand(BigInt(10) ^ (digits - 1):(BigInt(10) ^ digits) - 1)
end
