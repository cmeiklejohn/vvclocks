%% @doc Provide a wrapper library which provides the same interface
%%      as riak_core's vclock library, but uses the vvclock library to
%%      support use of the verified version.
%%
%%      Manually stub out the natural/term conversion calls for the time
%%      being to optimize for testing the library with the current test
%%      suite.
%%

-module(vclock).
-author('Christopher Meiklejohn <christopher.meiklejohn@gmail.com>').

-export([fresh/0,
         descends/2,
         merge/1,
         get_counter/2,
         get_timestamp/2,
         increment/2,
         increment/3,
         all_nodes/1,
         equal/2,
         prune/3,
         timestamp/0]).

-export([peano_timestamp/0]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

%% @doc Return natural timestamp.
timestamp() ->
    calendar:datetime_to_gregorian_seconds(erlang:universaltime()).

%% @doc Peanoized timestamp.
peano_timestamp() ->
    term_to_peano(timestamp()).

%% @doc Generate a fresh vector clock.
fresh() ->
    vvclock:fresh().

%% @doc Increment a vector clock for a particular actor.
increment(Actor, VClock) ->
    vvclock:increment(term_to_peano(Actor), VClock).

%% @doc Increment a vector clock with a particular timestamp.
increment(_Actor, _Timestamp, _VClock) ->
    %% Not implementing this one for now.
    erlang:error(deprecated).

%% @doc Return counter for a particular actor.
get_counter(Actor, VClock) ->
    Counter = vvclock:get_counter(term_to_peano(Actor), VClock),
    peano_to_term(Counter).

%% @doc Return timestamp for a particular actor.
get_timestamp(Actor, VClock) ->
    Timestamp = vvclock:get_timestamp(term_to_peano(Actor), VClock),
    peano_to_term(Timestamp).

%% @doc Determine if one vector clock is an ancestor of another.
descends(VClock1, VClock2) ->
    case vvclock:descends(VClock1, VClock2) of
        'True' ->
            true;
        'False' ->
            false
    end.

%% @doc Return list of all actors that have ever touched the vclock.
all_nodes(VClock) ->
    [peano_to_term(Node) || Node <- vvclock:all_nodes(VClock)].

%% @doc Prune vclocks.
prune(VClock, _Timestamp, BProps) ->
    Old = get_property(old_vclock, BProps),
    Young = get_property(young_vclock, BProps),
    Large = get_property(large_vclock, BProps),
    Small = get_property(small_vclock, BProps),
    vvclock:prune(VClock, Small, Large, Young, Old).

%% @doc Merge function which operates on a list of vector clocks.
merge([VClock1,VClock2|VClocks]) ->
    merge([vvclock:merge(VClock1, VClock2)|VClocks]);
merge([VClock]) ->
    VClock;
merge([]) ->
    [].

%% @doc Compare equality of two vclocks.
equal(VClock1, VClock2) ->
    vvclock:equal(VClock1, VClock2).

%% @doc Convert a peano number back into an erlang term.
peano_to_term(Peano) ->
    natural_to_term(peano_to_natural(Peano)).

%% @doc Convert an erlang term into a peano number.
term_to_peano(Term) ->
    natural_to_peano(term_to_natural(Term)).

%% @doc Convert a natural number to an erlang term.
natural_to_term(Natural) ->
    case Natural of
        1 ->
            a;
        2 ->
            b;
        3 ->
            c;
        4 ->
            d;
        _ ->
            erlang:error(not_supported)
    end.

%% @doc Convert an erlang term to a natural number.
term_to_natural(Term) ->
    case Term of
        a ->
            1;
        b ->
            2;
        c ->
            3;
        d ->
            4;
        _ ->
            erlang:error(not_supported)
    end.

%% @doc Convert a natural number into a peano.
natural_to_peano(0) ->
    'O';
natural_to_peano(Natural) ->
    {'S', natural_to_peano(Natural - 1)}.

%% @doc Convert a peano number into a natural.
peano_to_natural('O') ->
    0;
peano_to_natural({'S', Peano}) ->
    1 + Peano.

%% @doc Extract property from bucket properties.
get_property(Key, PairList) ->
    case lists:keyfind(Key, 1, PairList) of
      {_Key, Value} ->
        Value;
      false ->
        undefined
    end.
