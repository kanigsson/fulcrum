package body Fulcrum with SPARK_Mode is

   function Sum_Acc (S : Seq) return Seq is
      Result : Seq (S'Range) := (others => 0);
   begin
      Result (S'First) := S (S'First);
      if S:'Length = 1 then
         return Result;
      end if;
      for Index in S'First + 1 .. S'Last loop
         Result (Index) := Result (Index - 1) + S (Index);
         pragma Loop_Invariant
           (Result (S'First) = S (S'First) and then
                (for all I in S'First + 1 .. Index =>
                     Result (I) = Result (I - 1) + S (I)));
      end loop;
      return Result;
   end Sum_Acc;

   function Sum_Acc_Rev (S : Seq) return Seq is
      Result : Seq (S'Range) := (others => 0);
      Acc : Integer := 0;
   begin
      for Index in reverse S'Range loop
         Result (Index) := Acc + S (Index);
         Acc := Result (Index);
      end loop;
      return Result;
   end Sum_Acc_Rev;

   function Find_Fulcrum (S : Seq) return Integer is
      Left_Sums : Seq := Sum_Acc (S);
      Right_Sums : Seq := Sum_Acc_Rev (S);
      Max : Integer := Left_Sums (S'First) - Right_Sums (S'First);
      Index : Integer := S'First;
   begin
      for I in S'First + 1 .. S'Last loop
         if Left_Sums (I) - Right_Sums (I) > Max then
            Max := Left_Sums (I) - Right_Sums (I);
            Index := I;
         end if;
         pragma Loop_Invariant
           ((for all K in S'First .. I =>
                Sum_Acc (S) (K) - Sum_Acc_Rev (S) (K) <=
                Sum_Acc (S) (Index) - Sum_Acc_Rev (S) (Index)));
      end loop;
      return Index;
   end Find_Fulcrum;
end Fulcrum;
