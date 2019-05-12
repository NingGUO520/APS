
type valeur = Vide | InN of int 
| Any 
;;
let allocn mem1 taille =
	
	let mem2 = Array.make taille Any in
	let mem3 = Array.append mem1 mem2 in 
		(Array.length mem1),mem3
;;

let string_of_valeur v = 
match v with
 Vide -> "Vide  "
| InN (n)-> "InN ("^(string_of_int n )^")"
| Any ->  "Any"
;;		
let modifer_mem mem1 a v = 
	if a < (Array.length mem1) then (
		print_endline ("set adresse "^(string_of_int a)^" valeur "^(string_of_valeur v));
		Array.set mem1 a v ; 
		mem1 )
	else failwith ("adresse "^(string_of_int a)^" n'existe pas dans la memoire" )
;;

let memoire = Array.make 0 Vide in 
let a, m = allocn memoire 5 in 
let m2 = modifer_mem m 5 (InN(3)) in 
for i = 0 to  ((Array.length m2) - 1) do
	print_endline (string_of_valeur (Array.get m2 i))

done

;;





	