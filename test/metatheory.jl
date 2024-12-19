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

function all_expand(node_id::NodeID, theory)
    node = InternedExpr.nc[][node_id]
    node == InternedExpr.nullnode && return(NodeID[])
    self = [r(node_id) for r in theory]
    
    self = filter(!isnothing, self)
    # length(filter)
    lefts = node.left == InternedExpr.nullid ? NodeID[] : all_expand(node.left, theory)
    rights = node.right == InternedExpr.nullid ? NodeID[] : all_expand(node.right, theory)
    lefts = isempty(lefts) ? [node.left] : lefts
    rights = isempty(rights) ? [node.right] : rights
    @show length(lefts), length(rights)
    if length(lefts) > 1 && length(rights) > 1
        childs_left = map(Iterators.product(lefts, [node.right])) do (l, r)
            intern!(OnlyNode(node.head, node.iscall, node.v, l, r))
        end |> vec
        childs_right = map(Iterators.product([node.left], rights)) do (l, r)
            intern!(OnlyNode(node.head, node.iscall, node.v, l, r))
        end |> vec

        childs = vcat(childs_left, childs_right)
    else 
        childs = map(Iterators.product(lefts, rights)) do (l, r)
            intern!(OnlyNode(node.head, node.iscall, node.v, l, r))
        end |> vec
    end
    # @show length(childs)
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


# all_expanded = all_expand(symex, theory)