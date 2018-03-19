/*
  Maxime Deroissart
  Daniel Sasu
*/

grillehex([[11,2,_,7,_,_,_,15,6,14,_,_,_,3,_,13], [_,_,_,9,11,_,2,_,_,_,_,_,15,1,_,6], [_,10,_,12,_,_,7,_,4,_,8,_,_,_,14,_], [_,8,_,3,_,_,1,_,_,_,15,12,10,_,4,2], [_,_,14,_,_,_,_,_,1,6,10,_,_,_,3,_], [3,_,_,_,_,_,_,_,_,4,_,15,8,_,6,11], [_,_,_,13,2,_,_,_,_,11,_,_,7,4,_,_], [_,11,8,4,0,_,_,13,7,_,9,3,14,_,_,_], [_,_,_,15,3,7,_,4,5,_,_,9,0,13,12,_], [_,_,12,8,_,_,10,_,_,_,_,11,4,_,_,_], [4,9,_,5,14,_,13,_,_,_,_,_,_,_,_,10], [_,13,_,_,_,6,12,1,_,_,_,_,_,7,_,_], [9,1,_,14,7,4,_,_,_,15,_,_,3,_,13,_], [_,3,_,_,_,9,_,2,_,1,_,_,5,_,0,_], [15,_,4,11,_,_,_,_,_,3,_,13,1,_,_,_], [5,_,13,_,_,_,15,14,9,_,_,_,2,_,11,4]]).


/* Question 1 */

% Version 1

printline([]):-write('|'), nl.
printline([H|L]):-var(H), write('|'), write(' '), printline(L).
printline([H|L]):-write('|'), write(H), printline(L).

% Version 2

printlinebis([]). %Si liste vide, alors on affiche rien.
printlinebis([X]):- integer(X), !, writeln(""|X|""). %Si un seul élément NUMERIQUE, alors on l affiche avant de retourner à la ligne.
printlinebis([_]):- ! ,writeln("| |").  %Sinon si un seul élément non instancié
printlinebis([H|T]):- integer(H), !,write(""|H),printlinebis(T). %Tant que liste non vide appel récursif de la fonction
printlinebis([_|T]):- !, write("| "),printlinebis(T). %Meme chose si variable non instanciée

/* Question 2 */
print([]). %Cas de base
print([H|T]):- printline(H), print(T). %Impression de chaque ligne

/* Question 3 */

% Version 1

bonnelongueur(L,N):-length(L,Length), Length == N.

% Version 2

bonnelongueurbis([],0). %Cas de base
bonnelongueurbis([_|T],N):-bonnelongueurbis(T,NN), N is NN+1. %Filtrage à gauche en décrémentant le compteur. Inutile de vérifier la tête

/* Question 4 */
bonnetaille([],_).  %Cas de base, la valeur de N importe peu.
bonnetaille([H|T], N):- bonnelongueur(H,N), bonnetaille(T,N). %Tant que liste non vide appel récursif de la fonction

?- use_module(library(clpfd)).

/* Question 5 */
verifie([]).
verifie([H|T]):- H ins 0..15, all_distinct(H), verifie(T).

/* Question 6 */

eclate([H],[],[[H]]). %Cas de base si vide
eclate([H|T],[],[[H]|L]):- eclate(T,[],L). %On ajoute en tête de L Chaque element sous forme de liste

eclate([],[],[]). %Cas de base
eclate([H|T], [HH|TT],[[H|HH]|L]):- eclate(T,TT,L). %Sous-liste = tête des deux listes ; Puis on rappelle récursivement la fct

/* Question 7 */

transp([],[]).
transp([H|T],L):- eclate(H,R,L),transp(T,R).

/* Question 8 */

decoupe([],[],[],[],_).
decoupe([W1,W2,W3,W4|T0],[X1,X2,X3,X4|T1],[Y1,Y2,Y3,Y4|T2],[Z1,Z2,Z3,Z4|T3],[[W1,W2,W3,W4,X1,X2,X3,X4,Y1,Y2,Y3,Y4,Z1,Z2,Z3,Z4]|L]):-decoupe(T0,T1,T2,T3,L).

/* Question 9 */
carres([],_).
carres([H1,H2,H3,H4|T],[L1,L2,L3,L4|TT]):- decoupe(H1,H2,H3,H4,[L1,L2,L3,L4]),carres(T,TT).

/* Question 10 */
solution(L):- bonnetaille(L,16),transp(L,R),bonnetaille(R,16),verifie(L),verifie(R), carres(L,C),verifie(C).

/* Question 11 */

