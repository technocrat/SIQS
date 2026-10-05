# ============================================================================
# siqs.jl — Self-Initializing Quadratic Sieve (SIQS) in Julia
# ----------------------------------------------------------------------------

using Random
using Printf
using Base: BitArray
include("number_theory.jl")
include("prime.jl")
include("utility.jl")
include("pollardrho.jl")

# ----------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------
const LOWER_BOUND_SIQS = Int32(2)
const UPPER_BOUND_SIQS = Int32(4000)
const SMALL_B = Int32(1024)

const MULT_LIST::Vector{UInt32} = UInt32[
    1, 2, 3, 5, 7, 9, 10, 11, 13, 14, 15, 17, 19, 21, 23, 25, 29, 31, 33, 35,
    37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71,
    73, 75, 77, 79, 83, 85, 87, 89, 91, 93, 95, 97, 101, 103, 105, 107, 109,
    111, 113, 115, 119, 121, 123, 127, 129, 131, 133, 137, 139, 141, 143, 145,
    147, 149, 151, 155, 157, 159, 161, 163, 165, 167, 173, 177, 179, 181, 183,
    185, 187, 191, 193, 195, 197, 199, 201, 203, 205, 209, 211, 213, 215, 217,
    219, 223, 227, 229, 231, 233, 235, 237, 239, 241, 249, 251, 253, 255,
]

# ----------------------------------------------------------------------------
# Data structures
# ----------------------------------------------------------------------------

"""One factor-base prime with its two sieve roots and log contribution."""
mutable struct FBPrime
    prime::UInt32
    root1::Int32
    root2::Int32
    logprime::UInt8
end

"""One SIQS polynomial Q(x) = a*x^2 + 2*b*x + c (b stored, 2b used in eval)."""
mutable struct Polynomial
    a::BigInt
    b::BigInt
    c::BigInt
    v::Int        # Gray-code index changed to obtain this polynomial (0-based)
    e::Int32      # Gray-code sign (+1 / -1)
end

"""The first polynomial of a batch plus the shared `b_list` / `a` factors."""
mutable struct PolyState
    a::BigInt
    b::BigInt
    c::BigInt
    b_list::Vector{BigInt}
    s::UInt32
    afact::Set{Int32}
end

mutable struct QsState
    n::BigInt
    b::UInt32
    m::UInt32
    t::UInt32
    update_frequency::UInt32
    verbose::Bool
    prime_limit::Int32
    eps::UInt32
    lp_multiplier::UInt32
    multiplier::UInt32
    root_map::Vector{Tuple{UInt32,UInt32}}
    lp_found::Int
    large_prime_bound::UInt32
    matrix::Vector{BigInt}
    relations::Vector{BigInt}
    roots::Vector{BigInt}
    partials::Dict{UInt64,Tuple{BigInt,Set{Int32},BigInt}}
    ind::BigInt
    sieve_values::Vector{UInt8}
    bainv::Vector{Vector{Int32}}
    poly_a_list::Set{BigInt}
    fb_primes::Vector{FBPrime}
    current_fb_primes::Vector{FBPrime}
    b1::Int
end

# ----------------------------------------------------------------------------
# Small helpers
# ----------------------------------------------------------------------------

"""Number of significant bits of |x|"""
@inline function significant_bits(x::BigInt)::UInt32
    iszero(x) && return UInt32(0)
    # ndigits with base 2 == bit length of |x|.
    return UInt32(ndigits(x, base=2))
end

"""Test bit `k` (0-based) of a non-negative `BigInt`"""
@inline function get_bit(x::BigInt, k::UInt32)::Bool
    return ((x >> k) & BigInt(1)) != 0
end

"""Least-significant set-bit index, or -1 when `x == 0`.
Mirrors `(x & -x).significant_bits() - 1` with the empty case giving -1.
"""
@inline function lsb_index(x::BigInt)::Int
    iszero(x) && return -1
    return Int(trailing_zeros(x))
end

"""Symmetric difference of two factor sets (mirrors `&a ^ &b` on hash sets)."""
function symdiff_sets(a::Set{Int32}, b::Set{Int32})::Set{Int32}
    out = Set{Int32}()
    for v in a
        v in b || push!(out, v)
    end
    for v in b
        v in a || push!(out, v)
    end
    return out
end

"""`f64 as u64` saturating cast (used for the ETA computation)."""
function f64_as_u64(x::Float64)::UInt64
    isnan(x) && return typemax(UInt64)
    x <= 0.0 && return UInt64(0)
    x >= 18446744073709551615.0 && return typemax(UInt64)
    return UInt64(trunc(x))
end

# ----------------------------------------------------------------------------
# Gray code
# ----------------------------------------------------------------------------

"""Gray-code table of length `2^(n-1)`; entry 0 is `(0, 0)`"""
function get_gray_code(n::Int)::Vector{Tuple{Int,Int32}}
    size = 1 << (n - 1)
    grays = Vector{Tuple{Int,Int32}}(undef, size)
    grays[1] = (0, Int32(0))
    for i in 1:(size-1)
        v = 1
        j = i
        while (j & 1) == 0
            v += 1
            j >>= 1
        end
        tmp = (i + ((1 << v) - 1)) >> v
        if (tmp & 1) == 1
            grays[i+1] = (v - 1, Int32(-1))
        else
            grays[i+1] = (v - 1, Int32(1))
        end
    end
    return grays
end

# ----------------------------------------------------------------------------
# Statistics printing
# ----------------------------------------------------------------------------

function print_stats(relations::Vector{BigInt}, target_relations::Int,
                     num_poly::UInt32, start_time::Float64,
                     first_time::Bool, lp_found::Int)
    if !first_time
        print("\x1B[13A\x1B[J")   # move up 13 lines + clear
        flush(stdout)
    end

    rel_len = Float64(length(relations))
    non_lp_rel_len = Float64(length(relations) - lp_found)
    num_poly_f64 = Float64(num_poly)
    elapsed = time() - start_time
    relations_per_polynomial = rel_len / num_poly_f64
    relations_per_second = rel_len / elapsed
    poly_per_second = num_poly_f64 / elapsed
    percent = (rel_len / Float64(target_relations)) * 100.0
    non_lp_percent = (non_lp_rel_len / Float64(target_relations)) * 100.0
    percent_per_second = percent / elapsed
    non_lp_percent_per_second = non_lp_percent / elapsed
    total_remaining_secs = f64_as_u64((100.0 - percent) / percent_per_second)
    hours = total_remaining_secs ÷ UInt64(3600)
    minutes = (total_remaining_secs % UInt64(3600)) ÷ UInt64(60)
    seconds = total_remaining_secs % UInt64(60)
    ehours = elapsed ÷ UInt64(3600)
    eminutes = (elapsed % UInt64(3600)) ÷ UInt64(60)
    eseconds = elapsed % UInt64(60)

    println("----------------------------------------------")
    println("Total Relations            : $(length(relations))    ")
    println("Total Partial Relations    : $(lp_found)    ")
    println("Total Polynomials Used     : $(num_poly)    ")
    @printf("Relations per Polynomial   : %.5f \n", relations_per_polynomial)
    @printf("Relations per Second       : %.2f \n", relations_per_second)
    @printf("Polynomials per Second     : %.2f \n", poly_per_second)
    @printf("Percent Complete           : %.5f%%\n", percent)
    @printf("Percent per Second         : %.5f%%\n", percent_per_second)
    @printf("Percent per Second (no LP) : %.5f%%\n", non_lp_percent_per_second)
    @printf("Estimated Time Remaining   : %d:%02d:%02d\n", hours, minutes, seconds)
    @printf("Elapsed Time               : %d:%02d:%02d\n", ehours, eminutes, eseconds)
    println("----------------------------------------------")
    flush(stdout)
end

# ----------------------------------------------------------------------------
# Parameter selection based on input size
# ----------------------------------------------------------------------------

function choose_params(n::BigInt)::Tuple{UInt32,UInt32,UInt32,UInt32}
    # returns (Factor Base Bound,Sieve Interval,eps,large prime multiplier)
    # based on size of input
    digits = ndigits(n)

    if digits <= 20
        return (3000, 16384, 25, 40)
    elseif digits <= 30
        return (4000, 16384, 25, 40)
    elseif digits <= 40
        return (10000, 16384, 25, 40)
    elseif digits <= 50
        return  (22000, 32767, 30, 50)
    elseif digits <= 60
        return  (45000, 52000, 48, 100)
    elseif digits <= 70
        return  (120000, 65536, 45, 150)
    elseif digits <= 75
        return (150000, 65536, 45, 150)
    elseif digits <= 80
        return (250000, 65536*2, 50, 150)
    elseif digits <= 90
        return (475000, 65536*2+32768, 60, 150)
    else
        return (1500000, 65536*9, 70, 150)
    end
end

# ----------------------------------------------------------------------------
# Multiplier selection
# ----------------------------------------------------------------------------

function choose_multiplier(qs_state::QsState,
                           multiplier::Base.RefValue{UInt32})::Vector{UInt32}
    n = qs_state.n
    b = qs_state.b
    prime_list = primes_less_than(b)
    if multiplier[] != UInt32(0)
        if qs_state.verbose println("Using multiplier k = $(multiplier[])") end
        return prime_list
    end

    ln2 = log(2.0)
    num_primes = min(length(prime_list), Int(300))

    nmod8 = UInt32(mod(n, BigInt(8)))

    scores = zeros(Float64, length(MULT_LIST))

    for (i, m) in enumerate(MULT_LIST)
        knmod8 = (nmod8 * m) % UInt32(8)
        logmult = log(Float64(m))
        scores[i] = 0.5 * logmult
        if knmod8 == UInt32(1)
            scores[i] -= 2.0 * ln2
        elseif knmod8 == UInt32(3)
            scores[i] -= 0.5 * ln2
        elseif knmod8 == UInt32(5)
            scores[i] -= ln2
        elseif knmod8 == UInt32(7)
            scores[i] -= 0.5 * ln2
        end
    end

    for k in 2:num_primes
        prime = prime_list[k]
        contrib = log(Float64(prime)) / (Float64(prime) - 1.0)
        modp = UInt32(mod(n, BigInt(prime)))
        for j in eachindex(MULT_LIST)
            knmodp = (modp * MULT_LIST[j]) % prime
            if knmodp == UInt32(0) || legendre(BigInt(knmodp), prime) == Int32(1)
                scores[j] -= knmodp == UInt32(0) ? contrib : 2.0 * contrib
            end
        end
    end

    mmap = collect(zip(scores, MULT_LIST))
    sort!(mmap, by = first)

    if qs_state.verbose
        for (score, mult) in mmap[1:5]
            println("Score: $(score), Multiplier: $(mult)")
        end
    end

    multiplier[] = mmap[1][2]
    if qs_state.verbose println("Using multiplier k = $(multiplier[])") end

    return prime_list
end

# ----------------------------------------------------------------------------
# Factor base
# ----------------------------------------------------------------------------

function build_factor_base(qs_state::QsState, prime_list::Vector{UInt32})
    factor_base = Int32[Int32(-1), Int32(2)]

    for k in 2:length(prime_list)
        prime = prime_list[k]
        if legendre(qs_state.n, prime) == Int32(1)
            push!(factor_base, Int32(prime))
            qs_state.root_map[Int(prime)+1] = tonelli_shanks(qs_state.n, prime)
            if Int32(prime) >= qs_state.prime_limit
                fbp = FBPrime(prime, Int32(0), Int32(0), UInt8(ndigits(prime, base=2) - 1))
                push!(qs_state.fb_primes, fbp)
            end
        end
    end

    factor_base_u128 = UInt128[UInt128(x) for x in factor_base[2:end]]
    factor_base_u64 = UInt64[UInt64(x) for x in factor_base[2:end]]
    factor_base_u32 = UInt32[UInt32(x) for x in factor_base[2:end]]

    if qs_state.verbose println("Factor base size: $(length(factor_base))") end
    return (factor_base, factor_base_u32, factor_base_u64, factor_base_u128)
end


# ----------------------------------------------------------------------------
# Polynomial `a` generation
# ----------------------------------------------------------------------------

function generate_a(qs_state::QsState, factor_base::Vector{Int32})
    poly_a_list = qs_state.poly_a_list
    lower_polypool_index::Int64 = 2
    upper_polypool_index::Int64 = min(Int64(SMALL_B) - 1, length(factor_base))
    poly_low_found = false
    for (i0, fb_prime) in enumerate(factor_base)
        idx0 = Int64(i0) - 1
        if idx0 > Int64(SMALL_B) - 1
            break
        end
        if fb_prime > LOWER_BOUND_SIQS && !poly_low_found
            lower_polypool_index = Int64(i0)
            poly_low_found = true
        end
        if fb_prime > UPPER_BOUND_SIQS
            upper_polypool_index = Int64(i0)
            break
        end
    end

    target_a = BigInt(0)
    target_bits = UInt32(0)
    if ndigits(qs_state.n) > 20
        target_a = isqrt(2 * qs_state.n) ÷ qs_state.m
        target_bits = UInt32(significant_bits(target_a))
        target_bits -= target_bits ÷ 10
    else
        target_a = isqrt(2 * qs_state.n)
        target_bits = UInt32(significant_bits(target_a))
    end

    too_close = UInt32(10) #3
    close_range = UInt32(5) #10
    poly_a = BigInt(1)
    afact = Set{Int32}()
    qli = Int[]

    a1 = BigInt(0)
    while true
        poly_a = BigInt(1)
        empty!(afact)
        empty!(qli)
        while true
            found_a_factor = false
            potential_a_factor::Int32 = Int32(1)
            randindex::Int = 1
            while !found_a_factor
                randindex = rand(Int(lower_polypool_index):Int(upper_polypool_index - 1))
                potential_a_factor = factor_base[randindex]
                found_a_factor = true
                if potential_a_factor in afact
                    found_a_factor = false
                end
            end
            poly_a *= BigInt(potential_a_factor)
            push!(afact, potential_a_factor)
            push!(qli, randindex)

            j = Int64(significant_bits(target_a)) - Int64(significant_bits(poly_a))
            if j < Int64(too_close)
                poly_a = BigInt(1)
                empty!(afact)
                empty!(qli)
                continue
            elseif j < Int64(too_close + close_range)
                break
            end
        end

        a1 = target_a ÷ poly_a
 
        mindiff = BigInt(typemax(UInt64))
        randindex = 0
        a1_min_fb_prime = BigInt(0)

        for i in 1:min(Int(SMALL_B), length(factor_base))
            a1_min_fb_prime = abs(a1 - BigInt(factor_base[i]))
            if a1_min_fb_prime < mindiff
                mindiff = a1_min_fb_prime
                randindex = i
            end
        end

        found_a_factor = false
        potential_a_factor = Int32(1)
        while !found_a_factor
            potential_a_factor = factor_base[randindex]
            found_a_factor = true
            if potential_a_factor in afact
                found_a_factor = false
            end
            if !found_a_factor
                randindex += 1
            end
        end

        if randindex > Int(SMALL_B)
            continue
        end

        poly_a *= BigInt(potential_a_factor)
        push!(afact, potential_a_factor)
        push!(qli, randindex)

        diff_bits = significant_bits(target_a - poly_a)
        if diff_bits < target_bits
            if poly_a in poly_a_list
                target_bits += UInt32(1)
                continue
            else
                break
            end
        end

        #=
        diff_bits = significant_bits(target_a - poly_a)
        if diff_bits < target_bits
            break
        end
        =#
    end
    push!(poly_a_list, poly_a)
    sort!(qli)
    return (poly_a, qli, afact)
end

# ----------------------------------------------------------------------------
# First polynomial of a batch
# ----------------------------------------------------------------------------

function generate_first_polynomial(qs_state::QsState,
                                   factor_base::Vector{Int32})::PolyState
    (a, qli, afact) = generate_a(qs_state, factor_base)
    bainv = qs_state.bainv
    s = length(qli)
    b_list = Vector{BigInt}(undef, s)
    for i in 1:s
        p = factor_base[qli[i]]
        r1 = Int32(qs_state.root_map[Int(p)+1][1])
        aq = a ÷ BigInt(p)
        invaq = modinv(aq, p)
        gamma = UInt32(mod(Int64(r1) * Int64(invaq), Int64(p)))
        if gamma > UInt32(p) ÷ UInt32(2)
            gamma = UInt32(p) - gamma
        end
        b_list[i] = aq * BigInt(gamma)
    end

    b = mod(sum(b_list), a)
    c = (b * b - qs_state.n) ÷ a

    res = BigInt(0)
    for fbp in qs_state.fb_primes
        p = Int32(fbp.prime)
        res = mod(a, BigInt(p))
        iszero(res) && continue
        p_u32 = UInt32(p)
        ainv = modinv(a, p)
        ainv2 = UInt64(mod(Int64(2) * Int64(ainv), Int64(p)))

        # store bainv
        for (j, b_val) in enumerate(b_list)
            value = UInt64(mod(b_val, BigInt(p_u32)))
            value = (value * ainv2) % UInt64(p)
            bainv[Int(p)+1][j] = Int32(value)
        end

        # store roots
        (r1_val, r2_val) = qs_state.root_map[Int(p_u32)+1]
        b_modp = UInt32(mod(b, BigInt(p_u32)))
        ainv_modp = UInt64(mod(Int64(ainv), Int64(p)))

        r1_modp = r1_val % p_u32
        diff_u64 = r1_modp >= b_modp ? UInt64(r1_modp - b_modp) :
                                       UInt64(p_u32) - UInt64(b_modp - r1_modp)
        r1 = UInt32((diff_u64 * ainv_modp) % UInt64(p))
        r1 = (r1 + qs_state.m) % p_u32

        r2_modp = r2_val % p_u32
        diff_u64 = r2_modp >= b_modp ? UInt64(r2_modp - b_modp) :
                                       UInt64(p_u32) - UInt64(b_modp - r2_modp)
        r2 = UInt32((diff_u64 * ainv_modp) % UInt64(p))
        r2 = (r2 + qs_state.m) % p_u32

        if r1 > r2
            r1, r2 = r2, r1
        end
        fbp.root1 = Int32(r1)
        fbp.root2 = Int32(r2)
    end

    return PolyState(a, b, c, b_list, UInt32(s), afact)
end

# ----------------------------------------------------------------------------
# Fast trial division over the factor base
# ----------------------------------------------------------------------------

"""Toggle a prime's presence (tracks square-free parity)."""
@inline function toggle_factor!(factors::Set{Int32}, f::Int32)
    if f in factors
        delete!(factors, f)
    else
        push!(factors, f)
    end
end

function factorise_fast(value::BigInt, factor_base_u32::Vector{UInt32},
                        factor_base_u64::Vector{UInt64},
                        factor_base_u128::Vector{UInt128})
    factors = Set{Int32}()

    if value < 0
        push!(factors, Int32(-1))
        value = -value
    end

    i = 1
    comp = BigInt(typemax(UInt128))

    while i <= length(factor_base_u32)
        factor = factor_base_u32[i]
        while mod(value, BigInt(factor)) == 0
            toggle_factor!(factors, Int32(factor))
            value = value ÷ BigInt(factor)
        end
        i += 1
        if value < comp
            break
        end
    end

    if i == length(factor_base_u128) + 1
        return (factors, value)
    end

    val_u128 = UInt128(value)

    while i <= length(factor_base_u128)
        factor = factor_base_u128[i]
        while val_u128 % factor == UInt128(0)
            toggle_factor!(factors, Int32(factor))
            val_u128 = val_u128 ÷ factor
        end
        i += 1
        if val_u128 < UInt128(typemax(UInt64))
            break
        end
    end

    if i == length(factor_base_u128) + 1
        return (factors, BigInt(val_u128))
    end

    val_u64 = UInt64(val_u128)

    while i <= length(factor_base_u64)
        factor = factor_base_u64[i]
        while val_u64 % factor == UInt64(0)
            toggle_factor!(factors, Int32(factor))
            val_u64 = val_u64 ÷ factor
        end
        i += 1
    end

    return (factors, BigInt(val_u64))
end

# ----------------------------------------------------------------------------
# Polynomial batch generation (Gray-code walk)
# ----------------------------------------------------------------------------

function generate_polynomials(qs_state::QsState, polynomials::Vector{Polynomial},
                              factor_base::Vector{Int32},
                              grays::Vector{Tuple{Int,Int32}})::PolyState
    empty!(qs_state.current_fb_primes)
    empty!(polynomials)
    poly_state = generate_first_polynomial(qs_state, factor_base)
    stop = 1 << (Int(poly_state.s) - 1)

    found = false
    for fbp in qs_state.fb_primes
        pa = mod(poly_state.a, BigInt(fbp.prime))
        if !iszero(pa)
            push!(qs_state.current_fb_primes,
                  FBPrime(fbp.prime, fbp.root1, fbp.root2, fbp.logprime))
        end
        if !found && fbp.prime > (qs_state.m * UInt32(2) + UInt32(1))
            found = true
            qs_state.b1 = length(qs_state.current_fb_primes) - 1  # keep 0-based
        end
    end

    if !found
        qs_state.b1 = length(qs_state.current_fb_primes)
    end

    (v, e) = grays[2]
    push!(polynomials, Polynomial(poly_state.a, poly_state.b, poly_state.c, v, e))
    for i in 1:(stop-1)
        (vn, en) = grays[i+2]
        poly_curr = Polynomial(poly_state.a, polynomials[i].b, BigInt(0), vn, en)
        (v, e) = grays[i+1]
        poly_curr.b += BigInt(2) * BigInt(e) * poly_state.b_list[v+1]
        poly_curr.c = (poly_curr.b * poly_curr.b - qs_state.n) ÷ poly_curr.a
        push!(polynomials, poly_curr)
    end
    return poly_state
end

# ----------------------------------------------------------------------------
# Relation finding
# ----------------------------------------------------------------------------

function find_relations(qs_state::QsState, fb_map::Dict{Int32,Int},
                        interval_size::Int, poly_state::PolyState,
                        ppoly::Polynomial, factor_base_u32::Vector{UInt32},
                        factor_base_u64::Vector{UInt64},
                        factor_base_u128::Vector{UInt128})
    sieve_values = qs_state.sieve_values
    # Reinterpret the u8 sieve as u64 words.
    nwords = length(sieve_values) ÷ 8
    slice = reinterpret(UInt64, @view sieve_values[1:(nwords*8)])

    sieve_mask::UInt64 = 0x8080808080808080

    x = 0
    i = 1
    while x < interval_size
        if (i - 1) + 7 >= length(slice)
            break
        end

        to_mask = slice[i] | slice[i+1] | slice[i+2] | slice[i+3] |
                  slice[i+4] | slice[i+5] | slice[i+6] | slice[i+7]
        if to_mask & sieve_mask == UInt64(0)
            x += 64
            i += 8
            continue
        end
        i += 8
        for xv in x:(x+63)
            if xv >= length(sieve_values)
                break
            end
            if sieve_values[xv+1] < UInt8(0x80)
                continue
            end

            xval = Int32(xv) - Int32(qs_state.m)

            axval = ppoly.a * BigInt(xval)
            relation = axval + ppoly.b

            # Q(x) = a*x^2 + 2*b*x + c evaluated via (2b + a*x)*x + c.
            poly_val = BigInt(2) * ppoly.b + axval
            poly_val = poly_val * BigInt(xval) + ppoly.c

            # Value whose square root is tracked for the congruence.
            pva = poly_val * ppoly.a

            (local_factors, finval) = factorise_fast(poly_val, factor_base_u32,
                                                     factor_base_u64,
                                                     factor_base_u128)
            local_factors = symdiff_sets(local_factors, poly_state.afact)

            # Handle large primes and partial relations.
            if finval != 1
                if finval < BigInt(qs_state.large_prime_bound)
                    value = UInt64(finval)
                    if haskey(qs_state.partials, value)
                        (rel, lf, pv) = qs_state.partials[value]
                        relation = relation * rel
                        local_factors = symdiff_sets(local_factors, lf)
                        pva = pva * pv
                        qs_state.lp_found += 1
                    else
                        qs_state.partials[value] = (relation, local_factors, pva)
                        continue
                    end
                else
                    continue
                end
            end

            for fac in local_factors
                idx = fb_map[fac]
                qs_state.matrix[idx] = qs_state.matrix[idx] | qs_state.ind
            end

            qs_state.ind <<= 1
            push!(qs_state.relations, relation)
            push!(qs_state.roots, pva)

            if length(qs_state.relations) >= Int(qs_state.b) + Int(qs_state.t)
                break
            end
        end
        x += 64
    end
end

# ----------------------------------------------------------------------------
# Interval sieving
# ----------------------------------------------------------------------------

function interval_sieve(qs_state::QsState, v::Int, e::Int32, interval_size::Int)
    sieve_values = qs_state.sieve_values
    bainv = qs_state.bainv

    # split current_fb_primes at b1 (0-based)
    #   cur_fb1 = indices 1..b1, cur_fb2 = indices (b1+1)..end.
    for idx in 1:length(qs_state.current_fb_primes)
        fbp = qs_state.current_fb_primes[idx]
        p = Int(fbp.prime)
        p_i32 = Int32(p)

        r1 = Int(fbp.root1)
        r2 = Int(fbp.root2)
        log_p = fbp.logprime
        ebainv = Int(bainv[p+1][v+1]) * Int(e)
        fbp.root1 = Int32(mod(r1 - ebainv, p))
        fbp.root2 = Int32(mod(r2 - ebainv, p))

        if r1 > r2
            r1, r2 = r2, r1
        end
        if idx <= qs_state.b1
            # First (small-prime) part: sieve every multiple.
            while r2 < interval_size
                sieve_values[r1+1] = sieve_values[r1+1] + log_p  # wraps mod 256
                sieve_values[r2+1] = sieve_values[r2+1] + log_p
                r1 += p
                r2 += p
            end
            if r1 < interval_size
                sieve_values[r1+1] = sieve_values[r1+1] + log_p
            end
        else
            # Second (large-prime) part: at most one hit per root.
            if r1 < interval_size
                sieve_values[r1+1] = sieve_values[r1+1] + log_p
                if r2 < interval_size
                    sieve_values[r2+1] = sieve_values[r2+1] + log_p
                end
            end
        end
    end
end

# ----------------------------------------------------------------------------
# Main sieving loop
# ----------------------------------------------------------------------------

function sieve(qs_state::QsState, factor_base::Vector{Int32},
               factor_base_u32::Vector{UInt32}, factor_base_u64::Vector{UInt64},
               factor_base_u128::Vector{UInt128})
    start = time()
    dc = ndigits(qs_state.n)
    fb_len = length(factor_base)
    fb_map = Dict{Int32,Int}(val => i for (i, val) in enumerate(factor_base))
    target_relations = fb_len + Int(qs_state.t)
    qs_state.large_prime_bound = qs_state.b * qs_state.lp_multiplier

    # threshold = floor(log2(sqrt(n) * m) - eps), 53-bit floats.
    threshold_f = setprecision(53) do
        Float64(floor(log2(sqrt(BigFloat(qs_state.n)) * BigFloat(qs_state.m)) -
                      BigFloat(qs_state.eps)))
    end
    threshold = UInt8(clamp(threshold_f, 0.0, 255.0))
    bound = UInt8(0x80) - threshold

    qs_state.matrix = [BigInt(0) for _ in 1:fb_len]

    num_poly = UInt32(0)
    interval_size = Int(2 * qs_state.m + UInt32(1))
    grays = get_gray_code(20)

    qs_state.sieve_values = fill(bound, interval_size)

    ft = true
    polynomials = Polynomial[]
    while length(qs_state.relations) < target_relations
        if qs_state.verbose
            if num_poly % qs_state.update_frequency == UInt32(0)
                print_stats(qs_state.relations, target_relations, num_poly,
                            start, ft, qs_state.lp_found)
            end
        end
        ft = false
        poly_state = generate_polynomials(qs_state, polynomials, factor_base, grays)
        for ppoly in polynomials
            interval_sieve(qs_state, ppoly.v, ppoly.e, interval_size)
            find_relations(qs_state, fb_map, interval_size, poly_state, ppoly,
                           factor_base_u32, factor_base_u64, factor_base_u128)
            num_poly += UInt32(1)
            fill!(qs_state.sieve_values, bound)
        end
    end
    if qs_state.verbose
        println("Large Primes Found: $(qs_state.lp_found)")
        println("Normal Relations Found: $(length(qs_state.relations) - qs_state.lp_found)")
    end
end

# ----------------------------------------------------------------------------
# Null-space extraction (Gaussian elimination over GF(2))
# ----------------------------------------------------------------------------

function null_space_extraction(qs_state::QsState)::Vector{BigInt}
    n = length(qs_state.relations)
    m = length(qs_state.matrix)
    t = Int(qs_state.t)

    matrix = qs_state.matrix
    marks = Int[]
    mark_mask = BigInt(0)
    cur = -1

    for i in 1:m
        if qs_state.verbose
            if cur % 10 == 0
                print("$(cur), $(m)\r")
            end
        end
        cur += 1
        lsb = lsb_index(matrix[i])
        if lsb == -1
            continue
        end
        push!(marks, n - lsb - 1)
        mark_mask = mark_mask | (BigInt(1) << lsb)

        pivot_row = matrix[i]
        for j in 1:m
            if get_bit(matrix[j], UInt32(lsb)) && Int(j) - 1 != cur
                matrix[j] = xor(matrix[j], pivot_row)
            end
        end
    end

    sort!(marks)
    nulls = BigInt[]
    mark_set = Set(marks)
    free_cols = Int[val for val in 0:(n-1) if !(val in mark_set)]
    k = 0
    for col in free_cols
        shift = n - col - 1
        val = BigInt(1) << shift
        fin = val
        for i in 1:m
            if get_bit(matrix[i], UInt32(shift))
                fin = fin | (matrix[i] & mark_mask)
            end
        end
        push!(nulls, fin)
        k += 1
        if k == t
            break
        end
    end
    return nulls
end

# ----------------------------------------------------------------------------
# Factor extraction from null-space dependencies
# ----------------------------------------------------------------------------

function extract_factors(qs_state::QsState, nulls::Vector{BigInt},
                         original_n::BigInt)
    n = length(qs_state.relations)
    bit = BigInt(0)
    for vector in nulls
        v = vector
        prod_right = BigInt(1)
        prod_left = BigInt(1)
        for idx in 1:n
            bit = v & BigInt(1)
            v >>= 1
            if bit == 1
                prod_left *= qs_state.relations[idx]
                prod_right *= qs_state.roots[idx]
            end
        end
        sqrt_right = isqrt(prod_right)
        prod_left = mod(prod_left, qs_state.n)
        sqrt_right = mod(sqrt_right, qs_state.n)
        gcd_input = prod_left - sqrt_right
        factor_candidate = gcd(original_n, gcd_input)
        if factor_candidate != 1 && factor_candidate != original_n
            other_factor = original_n ÷ factor_candidate
            return (factor_candidate, other_factor)
        end
    end
    return (BigInt(0), BigInt(0))
end

# ----------------------------------------------------------------------------
# Top-level driver
# ----------------------------------------------------------------------------

function qsfactor(qs_state::QsState)::Tuple{BigInt,BigInt}
    original_n = qs_state.n
    overall_start = time()
    if qs_state.verbose
        println("========== Self Initializing Quadratic Sieve Start ==========")
        println("Factoring N           = $(qs_state.n) ($(ndigits(qs_state.n)) digits) ($(significant_bits(qs_state.n)) bits)")
        println("Using B               = $(qs_state.b)")
        println("Using M               = $(qs_state.m)")
        println("Using prime_limit     = $(qs_state.prime_limit)")
        println("Using eps             = $(qs_state.eps)")
        println("Using lp_multiplier   = $(qs_state.lp_multiplier)")
    end
    step_start = time()
    mult_ref = Ref(qs_state.multiplier)
    prime_list = choose_multiplier(qs_state, mult_ref)
    qs_state.multiplier = mult_ref[]
    step_end = time() - step_start
    if qs_state.verbose @printf("Step 1 (Choose Multiplier) took %.3f seconds\n", step_end) end
    qs_state.n = qs_state.n * BigInt(qs_state.multiplier)

    step_start = time()
    (factor_base, factor_base_u32, factor_base_u64, factor_base_u128) =
        build_factor_base(qs_state, prime_list)
    step_end = time() - step_start
    if qs_state.verbose @printf("Step 2 (Build Factor Base) took %.3f seconds\n", step_end) end

    step_start = time()
    sieve(qs_state, factor_base, factor_base_u32, factor_base_u64, factor_base_u128)
    step_end = time() - step_start
    if qs_state.verbose @printf("Step 3 (Sieving) took %.3f seconds\n", step_end) end

    step_start = time()
    nulls = null_space_extraction(qs_state)
    step_end = time() - step_start
    if qs_state.verbose @printf("Step 4 (Null Space Extraction) took %.3f seconds\n", step_end) end

    step_start = time()
    (fa, fb) = extract_factors(qs_state, nulls, original_n)
    step_end = time() - step_start
    if qs_state.verbose @printf("Step 5 (Extract Factors) took %.3f seconds\n", step_end) end
    if qs_state.verbose print_elapsed_time(time() - overall_start) end
    (fa, fb)
end

# ----------------------------------------------------------------------------
# Find two factors of a semi-prime
# ----------------------------------------------------------------------------

function factor(nn::BigInt, verbose::Bool=false)::Tuple{BigInt,BigInt}
    # returns a tuple of two factors
    # returns (0,0) if no factors are found
    digit_count = ndigits(nn)
    if verbose println("digit count = ", digit_count) end

    if digit_count > 100
        println("Input must be 100 digits or less")
        return (BigInt(0), BigInt(0))
    end

    # check for input that would cause factorization to fail (negative value, prime number and integer power)
    if nn < 0
        println("Input must be positive")
        return (BigInt(0), BigInt(0))
    end

    if nn == 1
        return (BigInt(1), BigInt(1))
    end

    if isprime(nn)
        println("Input is a prime number")
        return (BigInt(nn), BigInt(1))
    end

    p = ispower(nn)
    if p != 0
        println("Input is an integer power")
        return (p, nn ÷ p)
    end

    
    # find factors 5 or less digits
    primes_5digit = primes_less_than(UInt32(100_000))
    for prime in primes_5digit
        if nn % prime == 0
            return (BigInt(prime), nn ÷ prime)
        end
    end

    
    # use pollard rho algorithm for small numbers
    if digit_count <= 18
        if verbose println("Using pollard rho algorithm") end
        start_time = time()
        fa = pollardrho(nn)
        if verbose print_elapsed_time(time() - start_time) end
        return (fa, nn ÷ fa)
    end
    
    
    # now have a larger number, use SIQS

    # parameters automatically chosen
    # b, factor base bound (upper prime number limit for factor base)
    # m, sieve interval
    # eps, efficiency/optimizing parameter
    # lp_multiplier, large prime multiplier
    (b, m, eps, lp_multiplier) = choose_params(nn)

    t = UInt32(64) # extra relations to collect
    update_frequency = digit_count >= 80 ? 1 : 10 # update stats every one or every 10 times
    prime_limit = Int32(220) # minimum prime to be sieved
    multiplier = UInt32(0) # multiplier selection, leave zero for automatic selection
    root_map = fill((UInt32(0), UInt32(0)), Int(b) + 1)
    lp_found = 0
    large_prime_bound = UInt32(0)
    matrix = BigInt[]
    relations = BigInt[]
    roots = BigInt[]
    partials = Dict{UInt64,Tuple{BigInt,Set{Int32},BigInt}}()
    ind = BigInt(1)
    sieve_values = UInt8[]
    bainv = [zeros(Int32, 40) for _ in 1:(Int(b) + 1)]
    poly_a_list = Set{BigInt}()
    fb_primes = FBPrime[]
    current_fb_primes = FBPrime[]

    qs_state = QsState(nn, b, m, t, update_frequency, verbose, prime_limit, eps,
                    lp_multiplier, multiplier, root_map, lp_found, large_prime_bound,
                    matrix, relations, roots, partials, ind, sieve_values, bainv,
                    poly_a_list, fb_primes, current_fb_primes, 0)
                    
    qsfactor(qs_state)
end

# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

function main()
    # uncomment for command line input
    #if length(ARGS) > 0
    #    nn  = parse(BigInt, ARGS[1])
    #end

    # some test numbers, uncomment one to use along with the parse line
    #n = "490516739493812924575428019499" # 30 digits
    #n = "3009945328299388957931300315646308313419" # 40 digits
    #n = "32466092539065621597006224985875602441118457873449" # 50 digits
    n = "750014700584359514878998176863189936656347267709304336104953" # 60 digits
    #n = "3821588930350792167954816009780238547235939701293631242896458394309323" # 70 digits
    #n = "444165670830100364807708934724975053225119501482759395905805810135248970251" # 75 digits
    #n = "32359223112252035483026442913476041867810505843753089370355888993328247493431081" # 80 digits
    #n = "210282352803628314297444623664410288223068234485244872675057323275627391582812832505918087" # 90 digits
    #n = "1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139" # rsa-100
    nn = parse(BigInt, n)

    #=
    # next 3 lines will create a random semi-prime
    nn = 0
    while true
        p = randomprime(5)
        q = randomprime(5)
        nn = p * q
        ndigits(nn) == 10 && break
    end
    =#

    (fa,fb) = factor(nn, true)
    if fa == BigInt(0)
        println("No factors found")
        exit(0)
    else
        println("Non-trivial factors found: $(nn) = $(fa) x $(fb)")
    end
end

#for i in 1:1000
main()
#end