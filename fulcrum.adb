package body Fulcrum with SPARK_Mode is

   function Sum_Acc (S : Seq) return Sum_Type is
      Result : Sum_Type (S'Range) := (others => 0);
   begin
      Result (S'First) := S (S'First);
      if S'Length = 1 then
         return Result;
      end if;
      for Index in S'First + 1 .. S'Last loop
         pragma Loop_Invariant
           (Result (S'First) = S (S'First) and then
                (for all I in S'First + 1 .. Index - 1 =>
                     Result (I) = Result (I - 1) + S (I)));
         pragma Loop_Invariant (
            (for all I in S'First .. Index - 1 =>
               abs (Result (I)) <= I * Int'Last));
         Result (Index) := Result (Index - 1) + S (Index);
      end loop;
      return Result;
   end Sum_Acc;

   function Sum_Acc_Rev (S : Seq) return Sum_Type is
      Result : Sum_Type (S'Range) := (others => 0);
   begin
      Result (S'Last) := 0;
      if S'Length = 1 then
         return Result;
      end if;
      for Index in reverse S'First .. S'Last - 1 loop
         pragma Loop_Invariant
           (Result (S'Last) = 0 and then
                (for all I in Index + 1 .. S'Last - 1 =>
                     Result (I) = Result (I + 1) + S (I + 1)));
         pragma Loop_Invariant (
            (for all I in Index + 1 .. S'Last =>
               abs (Result (I)) <= (S'Last - I + 1) * Int'Last));
         Result (Index) := Result (Index + 1) + S (Index + 1);
      end loop;
      return Result;
   end Sum_Acc_Rev;

   function Sum (S : Seq) return Integer
      with Pre => S'Length > 0,
      Post =>
        Sum'Result = Sum_Acc_Rev (S) (S'First);

   function Sum (S : Seq) return Integer is
      Result : Integer := 0;
   begin
      for Index in reverse S'First + 1 .. S'Last loop
         pragma Loop_Invariant (Result = Sum_Acc_Rev (S) (Index));
         Result := Result + S (Index);
      end loop;
      return Result;
   end Sum;

  function Find_Fulcrum (S : Seq) return Nat is
     Index : Nat := S'First;
     Left_Sum : Integer := S (S'First);
     Right_Sum : Integer := Sum (S);
     Max : Integer := Left_Sum - Right_Sum;
  begin
     for I in S'First + 1 .. S'Last loop
        pragma Loop_Invariant
          (Left_Sum = Sum_Acc (S) (I - 1) and then
           Index in S'Range and then
           Right_Sum = Sum_Acc_Rev (S) (I - 1) and then
           Max = Sum_Acc (S) (Index) - Sum_Acc_Rev (S) (Index) and then
          (for all K in S'First .. I - 1 =>
               Sum_Acc (S) (K) - Sum_Acc_Rev (S) (K) <=
               Sum_Acc (S) (Index) - Sum_Acc_Rev (S) (Index)));
        Left_Sum := Left_Sum + S (I);
        Right_Sum := Right_Sum - S (I);
        pragma Assert (Left_Sum = Sum_Acc (S) (I));
        pragma Assert (Right_Sum = Sum_Acc_Rev (S) (I));
        if Left_Sum - Right_Sum > Max then
           Max := Left_Sum - Right_Sum;
           Index := I;
        end if;
        pragma Assert (
          (for all K in S'First .. I =>
               Sum_Acc (S) (K) - Sum_Acc_Rev (S) (K) <=
               Sum_Acc (S) (Index) - Sum_Acc_Rev (S) (Index)));
     end loop;
     return Index;
  end Find_Fulcrum;

end Fulcrum;
