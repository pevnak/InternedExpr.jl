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
        @show c, syc
        @test c isa NodeID
        if syc isa NodeID
            @test c == syc
        else
            @test expr(c) == syc
        end
    end
end

# theory


function old_expand(ex, theory, tmp::Vector)
    !(ex isa Expr) && return
    self = [r(ex) for r in theory]
    self = filter(!isnothing, self)
    append!(tmp , self)
    # for i in ex.args
    for i in ex.args
        old_expand(i, theory, tmp)
    end

    # length(ex.args) < 3 && ex.head != :call ? old_expand(ex.args[1], theory, tmp) : old_expand(ex.args[2], theory, tmp)
    # length(ex.args) < 3 && ex.head != :call ? old_expand(ex.args[2], theory, tmp) : old_expand(ex.args[3], theory, tmp)
    # end
end

# function all_expand(node::NodeID, theory)
#     return all_expand(node, theory)
# end

function all_expand(node_id::NodeID, theory, expr_cache::Dict{NodeID, Vector}=Dict{NodeID, Vector}())
    node = InternedExpr.nc[][node_id]
    !(node.iscall) && return(NodeID[])
    get!(expr_cache, node_id) do
        
    self = [r(node_id) for r in theory]
    
    self = convert(Vector{NodeID}, filter(!isnothing, self))
    # self = filter(x->x!=InternedExpr.nullnode, self)
    lefts = all_expand(node.left, theory, expr_cache)
    rights = all_expand(node.right, theory, expr_cache)
    lefts = isempty(lefts) ? [node.left] : lefts
    rights = isempty(rights) ? [node.right] : rights
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
    return vcat(self, childs)
    end
end

# symex, r = (:(100 + 10), @rule ~a::Number + ~b::Number => a + b)

# ex = intern!(symex)
# c = r(ex)
# syc = r(symex)
# c isa NodeID
# expr(c) == syc

ex = :((((((v0 - v1) + 15) / 8) * 8 + v1) - 4) - 116 <= ((((v0 + 16) - v2) + 6) / 135) * 135 + v2 && ((v3 - (v4 * 2 + v5)) + v4 * 2) + 64 <= (v3 - v5) + 64)
symex = intern!(ex)
# r = theory[20]
# r(symex)

using JSON
function load_data(data_path::String)
    train_data = JSON.parsefile(data_path)
end

function preprosses_data_to_expressions(raw_data)
    new_data = []
    for i in raw_data
        push!(new_data, Meta.parse(i[1]))
    end
    return new_data
end

train_data_path = "../MetaProject1/data/neural_rewrter/train.json"
train_data = isfile(train_data_path) ? load_data(train_data_path)[10_001:70_000] : load_data(test_data_path)[1:1000]
train_data = filter(x->!occursin("select", x[1]), train_data)
sorted_data = sort(train_data, by=x->length(x[1]))
train_data = preprosses_data_to_expressions(sorted_data)


ex = :(0 - 1 <= (v0 + 7) / 4)
# ex = :(510 - 1002 <= v0 * 16)
# ex = :(530 - 488 <= 1024)
# ex = :(0 == (7 + 14) / 520)
# ex = :(min(v0 * 2, 37) - 255 <= v0 * 2)
ex = :(v2 + 4 <= ((7 + 8) / 8) * 8 + (v0 + v1))
symex = intern!(ex)
all_expanded = filter(x->x!=symex, all_expand(symex, theory))
tmp = []
old_expanded = old_expand(ex, theory, tmp)
tmp = filter(x->x!=symex, tmp)
@test length(tmp) == length(all_expanded)
@assert 0 == 1



@testset begin
    for ex in train_data
        symex = intern!(ex)
        for r in theory
            s = r(symex)
            c = r(ex)
            if s isa Nothing
                @test c == s
            elseif c isa NodeID
                @test c == s
            else
                @test c == expr(s)
            end
                
        # all_expanded = filter(x->x!=symex, all_expand(symex, theory))
        # tmp = []
        # old_expanded = old_expand(ex, theory, tmp)
        # tmp = filter(x->x!=symex, tmp)
            # @test length(tmp) == length(all_expanded)
        end
    end
end

@testset begin
    for ex in train_data
        # @show ex
        symex = intern!(ex)
        all_expanded = filter(x->x!=symex, all_expand(symex, theory))
        tmp = []
        old_expanded = old_expand(ex, theory, tmp)
        tmp = filter(x->x!=symex, tmp)
        @test length(tmp) == length(all_expanded) || "error in $(ex)"
    end
end