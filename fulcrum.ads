package Fulcrum with SPARK_Mode is

   subtype Int is Integer range -1000 .. 1000;
   subtype Nat is Integer range 1 .. 1000;

   type Seq is array (Nat range <>) of Int;
   type Sum_Type is array (Nat range <>) of Integer;

   function Sum_Acc (S : Seq) return Sum_Type
     with Ghost,
     Pre => S'Length > 0,
     Post =>
     (Sum_Acc'Result'Length = S'Length and then
      Sum_Acc'Result'First = S'First and then
      (for all I in S'First .. S'Last =>
            abs (Sum_Acc'Result (I)) <= I * Int'Last) and then
      Sum_Acc'Result (S'First) = S (S'First) and then
      (for all I in S'First + 1 .. S'Last =>
            Sum_Acc'Result (I) = Sum_Acc'Result (I - 1) + S (I)));

   function Sum_Acc_Rev (S : Seq) return Sum_Type
     with Ghost,
     Pre => S'Length > 0,
     Post =>
     (Sum_Acc_Rev'Result'Length = S'Length and then
      Sum_Acc_Rev'Result'First = S'First and then
      (for all I in S'First .. S'Last =>
         abs (Sum_Acc_Rev'Result (I)) <= (S'Last - I + 1) * Int'Last) and then
      Sum_Acc_Rev'Result (S'Last) = 0 and then
      (for all I in S'First .. S'Last - 1 =>
            Sum_Acc_Rev'Result (I) = Sum_Acc_Rev'Result (I + 1) + S (I + 1)));

  function Find_Fulcrum (S : Seq) return Nat
  with Pre => S'Length > 0,
       Post =>
       (Find_Fulcrum'Result in S'Range and then
          (for all I in S'Range =>
               Sum_Acc (S) (I) - Sum_Acc_Rev (S) (I) <=
               Sum_Acc (S) (Find_Fulcrum'Result) - Sum_Acc_Rev (S) (Find_Fulcrum'Result)));

end Fulcrum;
