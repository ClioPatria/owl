/*  Part of ClioPatria SeRQL and SPARQL server

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@cs.vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2010, University of Amsterdam,
		   VU University Amsterdam

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/

:- module(owl_sameas,
	  [ owl_sameas/2,		% ?R1, ?R2
	    owl_sameas_partition/2,	% +List, -PowerSet
	    owl_sameas_representative/3,% +Algorithm, +Set, -Representative
	    owl_sameas_map/3		% +Algorithm, +List, -Assoc
	  ]).
:- use_module(library(semweb/rdf_db)).
:- use_module(library(ordsets)).
:- use_module(library(count)).
:- use_module(library(assoc)).

:- initialization
	rdf_set_predicate(owl:sameAs, symmetric(true)).

:- if((rdf_version(V),V<20900)).
:- multifile prolog:message//1.
prolog:message(rdf_version(MinVersion)) -->
	[ 'library(semweb/owl_sameas) requires version > ~w of RDF-DB'-
	  [MinVersion]
	].
:- print_message(error, rdf_version(20900)).
:- endif.

/** <module> Handle owl:sameAs predicates

This module provides predicates that perform  various operations on sets
of resources that are possibly connected through owl:sameAs reations.
*/

%%	owl_sameas(?R1, ?R2) is nondet.
%
%	True if R is equivalent to R0 through owl:sameAs properties.

owl_sameas(R1, R2) :-
	(   rdf_reachable(R1, owl:sameAs, R2)
	*-> true
	;   R1 = R2			% literals
	).

%%	owl_sameas_partition(+Resources, -PowerSet) is det.
%
%	True when each element  of  PowerSet   is  a  set  of equivalent
%	resources and there are no two equivalent resources in different
%	members of PowerSet.

owl_sameas_partition(Resources, PowerSet) :-
	sort(Resources, OrdSet),
	partition(OrdSet, PowerSet).

partition([], []).
partition([H|T], [Set0|Sets]) :-
	(   rdf_has(H, owl:sameAs, _)
	->  findall(R, owl_sameas(H, R), Eq),
	    sort(Eq, Set0),
	    ord_subtract(T, Set0, Rest),
	    partition(Rest, Sets)
	;   Set0 = [H],
	    partition(T, Sets)
	).

%%	owl_sameas_representative(+Algorithm, +List, -Representer)
%
%	True when Representer is a  member   of  Set that represents the
%	set. There is no unique way to  decide on the representer, which
%	is why we provide Algorithm to select a dedicated algorithm. The
%	current implementation has two algorihtms:
%
%	    * order
%	    Return the smallest resource in the standard order of terms.
%	    This is adequate for internal reasoning tasks.
%	    * default
%	    Find the most-connected resource that is not a blank node.
%	    If all resources are blank nodes, find the most connected
%	    one.

owl_sameas_representative(order, List, Representative) :-
	sort(List, [Representative|_]).
owl_sameas_representative(default, List, Representative) :-
	(   exclude(rdf_is_bnode, List, NonBNodes),
	    NonBNodes \== []
	->  representative(NonBNodes, Representative)
	;   representative(List, Representative)
	).

representative([H], Representative) :- !,
	Representative = H.
representative([H|T], Representative) :-
	fan_in_out(H, Fan0),
	best(T, Fan0, H, Representative).

best([], _, R, R).
best([H|T], S0, R0, R) :-
	fan_in_out(H, S1),
	(   S1 > S0
	->  best(T, S1, H, R)
	;   best(T, S0, R0, R)
	).

fan_in_out(R, Fan) :-
	proof_count(rdf(R, _, _), 100, FanOut),
	proof_count(rdf(_, _, R), 100, FanIn),
	Fan is FanOut + FanIn.


%%	owl_sameas_map(+Algorithm, +List, -Assoc) is det.
%
%	Creates an assoc that maps  each   resource  from  List onto its
%	_representative_. Only resources  that   are  connected  through
%	owl:sameAs are included in Assoc. This means:
%
%	  1. If a resource is not in the assoc, there is no equivalent
%	  in List.
%	  2. If the resource maps to itself, it is the representative
%	  and there are other resources that map to it.

owl_sameas_map(Algorithm, List, Assoc) :-
	owl_sameas_partition(List, Sets),
	map_list_to_pairs(owl_sameas_representative(Algorithm),
			  Sets, KeyedSets),
	empty_assoc(Assoc0),
	sameas_map(KeyedSets, Assoc0, Assoc).

sameas_map([], Assoc, Assoc).
sameas_map([_-[_]|T], Assoc0, Assoc) :- !,
	sameas_map(T, Assoc0, Assoc).
sameas_map([R-Eq|T], Assoc0, Assoc) :- !,
	ins_eq(Eq, Assoc0, R, Assoc1),
	sameas_map(T, Assoc1, Assoc).

ins_eq([], Assoc, _, Assoc).
ins_eq([H|T], Assoc0, R, Assoc) :-
	put_assoc(H, Assoc0, R, Assoc1),
	ins_eq(T, Assoc1, R, Assoc).
