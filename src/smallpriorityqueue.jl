#
# small priority queues
#

export MutableSmallPriorityQueue

struct MutableSmallPriorityQueue{N,K,V,O<:Base.Ordering} <: AbstractSmallDict{N,K,V}
    # Binary heap of (element, priority) pairs.
    xs::MutableSmallVector{N,Pair{K,V}}
    o::O

    # Map elements to their index in xs
    index::MutableSmallDict{N,K,Int}

    function MutableSmallPriorityQueue{N,K,V}(o::O) where {N,K,V,O<:Base.Ordering}
        new{N,K,V,O}(MutableSmallVector{N,Pair{K,V}}(), o, MutableSmallDict{N,K,Int}())
    end

    MutableSmallPriorityQueue(xs::AbstractSmallVector{N,Pair{K,V}}, o::O, index::AbstractSmallDict{N,K,Int}) where {N,K,V,O<:Base.Ordering} = new{N,K,V,O}(xs, o, index)
end

function MutableSmallPriorityQueue{N,K,V}(o::O, itr) where {N,K,V,O<:Base.Ordering}
    return foldl(push!, itr; init = MutableSmallPriorityQueue{N,K,V}(o))
end

Base.length(pq::MutableSmallPriorityQueue) = length(pq.xs)

Base.isempty(pq::MutableSmallPriorityQueue) = isempty(pq.xs)

Base.haskey(pq::MutableSmallPriorityQueue, key) = haskey(pq.index, key)

Base.first(pq::MutableSmallPriorityQueue) = first(pq.xs)

Base.keys(pq::MutableSmallPriorityQueue) = keys(pq.index)

Base.values(pq::MutableSmallPriorityQueue) = SmallVector(second.(pq.xs))


heapleft(i::Integer) = 2i
heapright(i::Integer) = 2i + 1
heapparent(i::Integer) = div(i, 2)

function percolate_down!(pq::MutableSmallPriorityQueue, i::Integer)
    x = pq.xs[i]
    @inbounds while (l = heapleft(i)) <= length(pq)
        r = heapright(i)
        j = r > length(pq) || Base.lt(pq.o, pq.xs[l].second, pq.xs[r].second) ? l : r
        xj = pq.xs[j]
        if Base.lt(pq.o, xj.second, x.second)
            pq.index[xj.first] = i
            pq.xs[i] = xj
            i = j
        else
            break
        end
    end
    pq.index[x.first] = i
    pq.xs[i] = x
end

function percolate_up!(pq::MutableSmallPriorityQueue, i::Integer)
    x = pq.xs[i]
    @inbounds while i > 1
        j = heapparent(i)
        xj = pq.xs[j]
        if Base.lt(pq.o, x.second, xj.second)
            pq.index[xj.first] = i
            pq.xs[i] = xj
            i = j
        else
            break
        end
    end
    pq.index[x.first] = i
    pq.xs[i] = x
end

# Equivalent to percolate_up! with an element having lower priority than any other
function force_up!(pq::MutableSmallPriorityQueue, i::Integer)
    x = pq.xs[i]
    @inbounds while i > 1
        j = heapparent(i)
        pq.index[pq.xs[j].first] = i
        pq.xs[i] = pq.xs[j]
        i = j
    end
    pq.index[x.first] = i
    pq.xs[i] = x
end


Base.getindex(pq::MutableSmallPriorityQueue, key) = pq.xs[pq.index[key]].second

function Base.get(pq::MutableSmallPriorityQueue, key, default)
    i = get(pq.index, key, 0)
    i == 0 ? default : pq.xs[i].second
end

function Base.get!(pq::MutableSmallPriorityQueue, key, default)
    i = get(pq.index, key, 0)
    if i == 0
        push!(pq, key => default)
        return default
    else
        return pq.xs[i].second
    end
end

function Base.setindex!(pq::MutableSmallPriorityQueue{N,K,V}, value, key) where {N,K,V}
    i = get(pq.index, key, 0)
    if i != 0
        @inbounds oldvalue = pq.xs[i].second
        pq.xs[i] = Pair{K,V}(key, value)
        if Base.lt(pq.o, oldvalue, value)
            percolate_down!(pq, i)
        else
            percolate_up!(pq, i)
        end
    else
        push!(pq, key => value)
    end
    return value
end

function Base.push!(pq::MutableSmallPriorityQueue{N,K,V}, pair::Pair{K,V}) where {N,K,V}
    key = pair.first
    if haskey(pq, key)
        throw(ArgumentError("MutableSmallPriorityQueue keys must be unique"))
    end
    push!(pq.xs, pair)
    pq.index[key] = length(pq)
    percolate_up!(pq, length(pq))

    return pq
end

Base.push!(pq::MutableSmallPriorityQueue{N,K,V}, kv::Pair) where {N,K,V} = push!(pq, Pair{K,V}(kv.first, kv.second))

function Base.popfirst!(pq::MutableSmallPriorityQueue)
    x = pq.xs[1]
    y = pop!(pq.xs)
    if !isempty(pq)
        @inbounds pq.xs[1] = y
        pq.index[y.first] = 1
        percolate_down!(pq, 1)
    end
    delete!(pq.index, x.first)
    return x
end

function Base.popat!(pq::MutableSmallPriorityQueue, key)
    idx = pq.index[key]
    force_up!(pq, idx)
    popfirst!(pq)
end

function Base.delete!(pq::MutableSmallPriorityQueue, key)
    popat!(pq, key)
    return pq
end

function Base.empty!(pq::MutableSmallPriorityQueue)
    empty!(pq.xs)
    empty!(pq.index)
    return pq
end

Base.empty(pq::MutableSmallPriorityQueue) = MutableSmallPriorityQueue(empty(pq.xs), pq.o, empty(pq.index))


mutable struct _PQIteratorState{N,K,V,O<:Base.Ordering}
    pq::MutableSmallPriorityQueue{N,K,V,O}
    _PQIteratorState{N,K,V,O}(pq::MutableSmallPriorityQueue{N,K,V,O}) where {N,K,V,O<:Base.Ordering} = new(pq)
end

_PQIteratorState(pq::MutableSmallPriorityQueue{N,K,V,O}) where {N,K,V,O<:Base.Ordering} = _PQIteratorState{N,K,V,O}(pq)

function _iterate(pq::MutableSmallPriorityQueue, state)
    (k, idx), i = state
    return (pq.xs[idx], i)
end
_iterate(::MutableSmallPriorityQueue, ::Nothing) = nothing

Base.iterate(::MutableSmallPriorityQueue, ::Nothing) = nothing

function Base.iterate(pq::MutableSmallPriorityQueue, ordered::Bool=true)
    if ordered
        isempty(pq) && return nothing
        state = _PQIteratorState(MutableSmallPriorityQueue(copy(pq.xs), pq.o, copy(pq.index)))
        return popfirst!(state.pq), state
    else
        _iterate(pq, iterate(pq.index))
    end
end

function Base.iterate(::MutableSmallPriorityQueue, state::_PQIteratorState)
    isempty(state.pq) && return nothing
    return popfirst!(state.pq), state
end

Base.iterate(pq::MutableSmallPriorityQueue, i) = _iterate(pq, iterate(pq.index, i))