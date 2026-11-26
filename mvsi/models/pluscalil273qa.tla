---------------------- MODULE pluscalil273q --------------------
\* CalculParalleleCanaux ----
EXTENDS Integers,Sequences,TLC
CONSTANTS
	special \* symbole spécial de marque de fin

(*--algorithm  calcul

variables
    A = <<1,2,3,4,5,6,7,8>>, \* affectation des données
    chan1 = <<>>, chan2 = <<>>, chan3 = <<>>, \* canaux  de communication
    chanR = <<>>,   \* canal  des  résultats
    eod = special,
     total = 0;
\* --------------== DISTRIBUTEUR ---------------------!
process P0 = "Distributeur"
variable i = 1;
begin
   w: while i <= Len(A) do
        if i % 3 = 1 then
            chan1 := Append(chan1, A[i]);
        elsif i % 3 = 2 then
            chan2 := Append(chan2, A[i]);
        else
            chan3 := Append(chan3, A[i]);
        end if;
        i := i + 1;
    end while;

    \* fin de données
    chan1 := Append(chan1, eod);
    chan2 := Append(chan2, eod);
    chan3 := Append(chan3, eod);
end process;



=============