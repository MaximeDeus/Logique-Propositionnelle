/*
  Maxime Deroissart
  Daniel Sasu
*/

grille([[_,_,_,_,_,_,_,_,_],
        [_,_,_,_,_,3,_,8,5],
        [_,_,1,_,2,_,_,_,_],
        [_,_,_,5,_,7,_,_,_],
        [_,_,4,_,_,_,1,_,_],
        [_,9,_,_,_,_,_,_,_],
        [5,_,_,_,_,_,_,7,3],
        [_,_,2,_,1,_,_,_,_],
        [_,_,_,_,4,_,_,_,9]]).

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
verifie([H|T]):- H ins 1..9, all_distinct(H), verifie(T).

/* Question 6 */

eclate([H],[],[[H]]). %Cas de base si vide
eclate([H|T],[],[[H]|L]):- eclate(T,[],L). %On ajoute en tête de L Chaque element sous forme de liste

eclate([],[],[]). %Cas de base
eclate([H|T], [HH|TT],[[H|HH]|L]):- eclate(T,TT,L). %Sous-liste = tête des deux listes ; Puis on rappelle récursivement la fct

/* Question 7 */

transp([],[]).
transp([H|T],L):- eclate(H,R,L),transp(T,R).

/* Question 8 */

decoupe([],[],[],_).
decoupe([X1,X2,X3|T1],[Y1,Y2,Y3|T2],[Z1,Z2,Z3|T3],[[X1,X2,X3,Y1,Y2,Y3,Z1,Z2,Z3]|L]):-decoupe(T1,T2,T3,L).

/* Question 9 */
carres([],_).
carres([H1,H2,H3|T],[L1,L2,L3|TT]):- decoupe(H1,H2,H3,[L1,L2,L3]),carres(T,TT).

/* Question 10 */
solution(L):- bonnetaille(L,9),transp(L,R),bonnetaille(R,9),verifie(L),verifie(R), carres(L,C),verifie(C).

/* Question 11 */
