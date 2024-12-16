
########################################################################
# Functions needed to hack rewriting systems
########################################################################
@inline car(t::NodeID) = operation(t)
@inline cdr(t::NodeID) = arguments(t)

function Rules.get_value(x::OnlyNode)
    x.head == :integer && return(Int32(x.v))
    x.head == :float && return(Float32(x.v))
    x.head
end

function typeof_value(x::OnlyNode)
    x.head == :integer && return(Int32)
    x.head == :float && return(Float32)
    x.left == nullid && return(Symbol)
    return(OnlyNode)
end
