function old_traverse_expr!(ex::Union{Expr,Symbol,Number}, matchers::Vector, tree_ind::Int, trav_indexs::Vector{Int}, tmp::Vector{Tuple{Vector{Int}, Int}}, caching::Dict{Expr, Vector})
    if !isa(ex, Expr)
        return
    end
    if haskey(caching, ex)
        b = copy(trav_indexs)
        append!(tmp, [(b, i) for i in caching[ex]])
        for (ind, i) in enumerate(ex.args)
            # Update the traversal index path with the current index
            push!(trav_indexs, ind)

            # Recursively traverse the sub-expression
            old_traverse_expr!(i, matchers, tree_ind, trav_indexs, tmp, caching)

            # After recursion, pop the last index to backtrack to the correct level
            pop!(trav_indexs)
        end
    end
    get!(caching, ex) do
        a = filter(em->!isnothing(em[2]), collect(enumerate(rt(ex) for rt in matchers)))
        if !isempty(a)
            b = copy(trav_indexs)
            append!(tmp, [(b, i[1]) for i in a])
        end

        # Traverse sub-expressions
        for (ind, i) in enumerate(ex.args)
            # Update the traversal index path with the current index
            push!(trav_indexs, ind)

            # Recursively traverse the sub-expression
            old_traverse_expr!(i, matchers, tree_ind, trav_indexs, tmp, caching)

            # After recursion, pop the last index to backtrack to the correct level
            pop!(trav_indexs)
        end
        return isempty(a) ? [] : [i[1] for i in a]
    end
end


function my_rewriter!(position::Vector{Int}, ex::Expr, rule)
    if isempty(position)
        return rule(ex) 
    end
    ind = position[1]
    ret = my_rewriter!(position[2:end], ex.args[ind], rule)
    if !isnothing(ret)
        ex.args[ind] = ret
    end
    return nothing
end


function execute(ex::Union{Expr, Number}, theory::Vector, caching::Dict{Expr, Vector}) 
    res = []
    tmp = Tuple{Vector{Int}, Int}[]
    old_traverse_expr!(ex, theory, 1, Int64[], tmp, caching) 
    for (pl, r) in tmp
        old_ex = copy(ex)
        o = my_rewriter!(pl, old_ex, theory[r])
        if isnothing(o)
            push!(res, ((pl, r), old_ex))
        else
            push!(res, ((pl, r), o))
        end
    end
    return res
end
