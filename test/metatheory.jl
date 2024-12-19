using InternedExpr
using InternedExpr.TermInterface
using InternedExpr.Rules
using Test
using Serialization
using Accessors

using InternedExpr: NodeID, intern!

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

theory


function all_expand(node::NodeID, theory)

end

function all_expand(node::OnlyNode, theory)
    self = [r(node) for r in theory]
    self = filter(!isnothing, self)

    node == InternedExpr.nullnode && return(NodeID[])
    lefts = all_expand(node.left, theory)
    rights = all_expand(node.rights, theory)
    lefts = isempty(lefts) ? [node.left] : lefts
    rights = isempty(rights) ? [node.right] : rights
    
    childs = map(Iterators.product(lefts, rights)) do (l, r)
        intern!(OnlyNode(node.head, node.call, node.value, l, r))
    end |> vec
    return vcat(self, childs)
end

# symex, r = (:(100 + 10), @rule ~a::Number + ~b::Number => a + b)

# ex = intern!(symex)
# c = r(ex)
# syc = r(symex)
# c isa NodeID
# expr(c) == syc


