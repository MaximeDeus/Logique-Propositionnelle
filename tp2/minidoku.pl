/*
  Maxime Deroissart
  Daniel Sasu
*/

grillehex([[2,_,_,3],
          [_,_,2,_],
          [_,4,1,_],
          [1,_,_,_]]).


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
verifie([H|T]):- H ins 1..4, all_distinct(H), verifie(T).

/* Question 6 */

eclate([H],[],[[H]]). %Cas de base si vide
eclate([H|T],[],[[H]|L]):- eclate(T,[],L). %On ajoute en tête de L Chaque element sous forme de liste

eclate([],[],[]). %Cas de base
eclate([H|T], [HH|TT],[[H|HH]|L]):- eclate(T,TT,L). %Sous-liste = tête des deux listes ; Puis on rappelle récursivement la fct

/* Question 7 */

transp([],[]).
transp([H|T],L):- eclate(H,R,L),transp(T,R).

/* Question 8 */

decoupe([],[],_).
decoupe([X1,X2|T1],[Y1,Y2|T2],[[X1,X2,Y1,Y2]|L]):-decoupe(T1,T2,L).

/* Question 9 */
carres([],_).
carres([H1,H2|T],[L1,L2|TT]):- decoupe(H1,H2,[L1,L2]),carres(T,TT).

/* Question 10 */
solution(L):- bonnetaille(L,4),transp(L,R),bonnetaille(R,4),verifie(L),verifie(R), carres(L,C),verifie(C).

/* Question 12 */

