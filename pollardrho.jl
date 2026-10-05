include("prime.jl")

# ----------------------------------------------------------------------------
# pollar rho factorization
# ----------------------------------------------------------------------------

function pollardrho(n::BigInt)
    # assumes n is positive and not prime ...
    g = n
    ys = BigInt()
    x = BigInt()
    while g == n
        y = rand(BigInt(1):n)
        c = rand(BigInt(1):n)
        m = rand(BigInt(1):n)
        g = q = 1
        r = 1
        while g == 1
            x, k = y, 0
            for i in 1:r
                y = (y^2 + c) % n
            end
            while k < r && g == 1
                ys = y
                for i in 1:min(m,r-k)
                    y = (y^2 + c) % n
                    q = q * abs(x-y) % n
                end
                g, k = gcd(q, n), k+m
            end
            r *= 2
        end
        if g == n
            while true
                ys = (ys^2+c) % n
                g = gcd(abs(x-ys), n)
                if g > 1
                    break
                end
            end
        end
    end
    return g
end

#=
p = randomprime(8)
q = randomprime(9)
n = p * q
println(p)
println(q)
println(n)
start = time()
factor = pollardrho(n)
println(time() - start)
println("factor = ", factor)
=#
