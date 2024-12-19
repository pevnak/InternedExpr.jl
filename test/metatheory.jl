using InternedExpr
using InternedExpr.TermInterface
using InternedExpr.Rules
using Test
using Serialization
using Accessors

using InternedExpr: NodeID, OnlyNode, intern!
include("test_theory.jl")

@testset "Rewriting rules" begin 

    testcases = [
        (:(2z), @rule 2(~x) --> ~x + ~x),
        (:(sin(2z)), @rule sin(2(~x)) --> 2sin(~x)*cos(~x)),
        (:(sin(x + y)), @rule sin(~x + ~y) --> sin(~x)*cos(~y) + cos(~x)*sin(~y)),
        (:(a <= a), @rule ~a <= ~a --> 1),
        (:(100 + 10), @rule ~a::Number + ~b::Number => a + b),
        (:(a && b), @rule ~a && ~b --> ~b && ~a),
        (:(a == b), @rule ~a == ~b => a != 0 && b != 0 ? intern!(:($a - $b == 0)) : intern!(:($a == $b))),
    ]


    for (symex, r) in testcases
        ex = intern!(symex)
        c = r(ex)
        syc = r(symex)
        @test c isa NodeID
        if syc isa NodeID
            @test c == syc
        else
            @test expr(c) == syc
        end
    end
end

theory


function all_expand(node::NodeID, theory)

end

function all_expand(node::NodeID, theory)
    self = [r(node) for r in theory]
    self = filter(!isnothing, self)

    node = InternedExpr.nc[][node]
    node == InternedExpr.nullnode && return(NodeID[])
    lefts = all_expand(node.left, theory)
    rights = all_expand(node.right, theory)
    lefts = isempty(lefts) ? [node.left] : lefts
    rights = isempty(rights) ? [node.right] : rights
    
    childs = map(Iterators.product(lefts, rights)) do (l, r)
        intern!(OnlyNode(node.head, node.iscall, node.v, l, r))
    end |> vec
    return vcat(self, childs)
end

# symex, r = (:(100 + 10), @rule ~a::Number + ~b::Number => a + b)

# ex = intern!(symex)
# c = r(ex)
# syc = r(symex)
# c isa NodeID
# expr(c) == syc

ex = :((((((v0 - v1) + 15) / 8) * 8 + v1) - 4) - 116 <= ((((v0 + 16) - v2) + 6) / 135) * 135 + v2 && ((v3 - (v4 * 2 + v5)) + v4 * 2) + 64 <= (v3 - v5) + 64)
symex = intern!(ex)
r = theory[20]
r(symex)