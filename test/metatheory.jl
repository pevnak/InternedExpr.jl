using StableExpr
using StableExpr.TermInterface
using StableExpr.Rules
using Test
using Serialization
using Accessors

using StableExpr: NodeID, intern!

@testset "Rewriting rules" begin 

    testcases = [
        (:(2z), @rule 2(~x) --> ~x + ~x),
        (:(sin(2z)), @rule sin(2(~x)) --> 2sin(~x)*cos(~x)),
        (:(sin(x + y)), @rule sin(~x + ~y) --> sin(~x)*cos(~y) + cos(~x)*sin(~y)),
        (:(a <= a), @rule ~a <= ~a --> 1),
        (:(100 + 10), @rule ~a::Number + ~b::Number => a + b),
    ]


    for (symex, r) in testcases
        ex = intern!(symex)
        c = r(ex)
        syc = r(symex)
        @test c isa NodeID
        @test expr(c) == syc
    end
end

# symex, r = (:(100 + 10), @rule ~a::Number + ~b::Number => a + b)

# ex = intern!(symex)
# c = r(ex)
# syc = r(symex)
# c isa NodeID
# expr(c) == syc


