% Très bon travail 4.5/5. Essayez d'améliorer votre style en prolog...
/*
  Maxime Deroissart
  Daniel Sasu
*/

/* Question 1 */
longueur([], 0).
longueur([_|Tail], Len):-
    longueur(Tail,Len1),
    Len is Len1 + 1.

/* Question 2 */
somme([], 0).
somme([Head | Tail], Sum):-
    somme(Tail, Sum1),
    Sum is Sum1 + Head.

/* Question 3 */
membre(X, [X|_]).
membre(X, [_|Tail]):-
     membre(X, Tail).

/* Question 4 */
ajoute_en_tete(X, List, FList):-
    FList = [X | List]. % Ici il aurait mieux valu écrire ajoute_en_tete(X, List, [X|List]).

/* Question 5 */
ajoute_en_queue(X, [], [X]).
ajoute_en_queue(X, [H|T], [H|Flist]):- ajoute_en_queue(X,T,Flist).

/* Question 6 */
extraire_tete([H|T], H, L):- ajoute_en_tete(H, T, [_|L]). % Vous auriez pu écrire extraire_tete(HL, H, L):- ajoute_en_tete(H, L, HL).

/* Question 7 */
concatene([],L,L).
concatene([X|Y],L,[X|R]):-concatene(Y,L,R).


/* Question 8 */
retourne([],C,C).
retourne([H|T],C, A):- retourne(T,[H|C],A).

/* Tris sur les listes */

/* Question 9 */
insert_trie(X,[],[X]).
insert_trie(E,[H|T],[E,H|T]) :- E =<H.
insert_trie(E,[H|T],[H|T1]) :- E > H, insert_trie(E,T,T1).


/* Question 10 */
tri_insert([],[]).
tri_insert([H|T],L1) :- tri_insert(T,L2),insert_trie(H,L2,L1).

/* Question 11 */
divise([], [], []).
divise([H], [H], []).
divise([H,HH|T],[H|L1],[HH|L2]):- divise(T,L1,L2).


/* Question 12 */
fusion(L1, [], L1).
fusion([], L1, L1).
fusion([H|T],[HH|TT],[H|L]):- H =< HH, fusion(T,[HH|TT],L).
fusion([H|T],[HH|TT],[HH|L]):- H > HH, fusion([H|T],TT,L).

/* Question 13 */
tri_fusion([],[]).
tri_fusion([H],[H]).
tri_fusion([H1,H2|T], L):- divise([H1,H2|T], L1, L2),
                           tri_fusion(L1, W),
                           tri_fusion(L2, E),
                           fusion(E,W,L).

/* Question 14 */
balance(_, [], [], []).
balance(P, [H|T], [H|L1], L2):- H =< P, balance(P, T, L1, L2).
balance(P, [H|T], L1, [H|L2]):- H > P, balance(P, T, L1, L2).


/* Question 15 */
tri_rapide([],[]).
tri_rapide([H|T], L):- balance(H, T, LL, LR),
                       tri_rapide(LL, Ll),
                       tri_rapide(LR, Lr),
                       concatene(Ll, [H|Lr], L).

/* Opérations de base sur les ensembles */

/* Question 16 */
est_vide(X) :- longueur(X, L), L==0. % Je préfèrerais est_vide([]).

/* Question 17 */
ajoute_ensemble(X, E, L):-not(membre(X,E)),ajoute_en_queue(X,E,L).
ajoute_ensemble(X, E, L):-membre(X,E),E=L. % Ici, ajoute_ensemble(X, E, E):-membre(X,E)
ajoute_ensemble(X,[],[X]). % Cette clause est inutile.

/* Question 18 */
sous_ensemble([],_).
sous_ensemble([H|T], E):- membre(H,E), sous_ensemble(T, E).

/* Question 19 */
union([],E, E).
union([H|T],E, L):-ajoute_ensemble(H,E,L),union(T,E,L).
union([H|T],E, [H|L]):-union(T,E,L).

/* Question 20 */
intersect([], _, []).
intersect([H1|T1], E2, [H1|L]):- membre(H1, E2), intersect(T1,E2, L).
intersect([_|T1], E2, L):-intersect(T1,E2,L). % Ici, il aurait fallu intersect([X|T1], E2, L):-not(membre(X,E2)), intersect(T1,E2,L).
                                 
/* Question 21 */
diff(T,[],T).
diff([],_,[]).
diff([H|T],E2,[H|L]):-not(membre(H,E2)), diff(T, E2, L).
diff([_|T],E2,L):-diff(T, E2, L). % Ici il aurait fallu diff([H|T],E2,L):-membre(H,E2), diff(T, E2, L).
