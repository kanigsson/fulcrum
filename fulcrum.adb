package body Fulcrum with SPARK_Mode is

   --  Straightforward implementation of Sum_Acc. The Loop_Invariants are just
   --  copies of the corresponding parts of the postcondition, using the loop
   --  index where appropriate.
   function Sum_Acc (S : Seq) return Sum_Type is
      Result : Sum_Type (S'Range) := (others => 0);
   begin
      Result (S'First) := S (S'First);
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

   --  A straightforward adaptation of [Sum_Acc] for the reverse case. Notice
   --  the loop traversing the loop indices in reverse order.
   function Sum_Acc_Rev (S : Seq) return Sum_Type is
      Result : Sum_Type (S'Range) := (others => 0);
   begin
      Result (S'Last) := 0;
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

   --  This is a helper function to compute the "right sum" of the array, that
   --  is, the sum of the array values without the first value. This function
   --  must run in O(1) space, so we don't use the Sum_Acc_Rev function (which
   --  is marked Ghost, so cannot be used in code anyway), but do another loop
   --  here. The postcondition, however, refers to Sum_Acc_Rev.
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

  --  Finally the implementation of Find_Fulcrum. It uses two variables
  --  Left_Sum and Right_Sum which contain the current values for those
  --  partial sums, as well as the variable Min for the current minimal
  --  difference between the sum, and the variable Index for the
  --  corresponding index.
  function Find_Fulcrum (S : Seq) return Nat is
     --  We initialize those four local variables, basically setting the
     --  current best index at the first cell of the array.
     Index : Nat := S'First;
     --  The first partial sum from the left is just the first cell of the
     --  array.
     Left_Sum : Integer := S (S'First);
     --  The first partial sum from the right uses the Sum function defined
     --  above; it corresponds to the sum of the entire array, excluding the
     --  first value. This is O(n) time, O(1) space.
     Right_Sum : Integer := Sum (S);
     --  The current best difference is just the first such difference.
     Min : Integer := abs (Left_Sum - Right_Sum);
  begin
     --  The code is now very straightforward. We iterate over the remainder
     --  of the array, adding the current value to the Left_Sum, and removing
     --  it from Right_Sum. We then compare their difference with the current
     --  best value Min, and update Min and Index if we found a new best
     --  value. This is clearly O(n) time. We don't do any calls or creation
     --  of new variables, so we stay at O(1) space.
     for I in S'First + 1 .. S'Last loop
        --  The loop invariants clearly express the intent of the four
        --  variables
        pragma Loop_Invariant
          --  we define what Left_Sum and Right_Sum are supposed to mean, that
          --  is, the partial sums as computed by Sum_Acc and Sum_Acc_Rev.
          (Left_Sum = Sum_Acc (S) (I - 1) and then
           Right_Sum = Sum_Acc_Rev (S) (I - 1) and then
          --  need to state that the Index variable is in range to be able to
          --  prove that the array accesses are within bounds
           Index in S'Range and then
          --  The link between Min and Index: Min contains the absolute
          --  difference between the partial sums at Index.
           Min = abs (Sum_Acc (S) (Index) - Sum_Acc_Rev (S) (Index)) and then
         --   and this is the best such difference up to now
          (for all K in S'First .. I - 1 =>
               abs (Sum_Acc (S) (K) - Sum_Acc_Rev (S) (K)) >=
               abs (Sum_Acc (S) (Index) - Sum_Acc_Rev (S) (Index))));
        Left_Sum := Left_Sum + S (I);
        Right_Sum := Right_Sum - S (I);
        --  the remaining three assertions are to help provers and just
        --  restate things that are already known.
        pragma Assert (Left_Sum = Sum_Acc (S) (I));
        pragma Assert (Right_Sum = Sum_Acc_Rev (S) (I));
        if abs (Left_Sum - Right_Sum) < Min then
           Min := abs (Left_Sum - Right_Sum);
           Index := I;
        end if;
        pragma Assert (
          (for all K in S'First .. I =>
               abs (Sum_Acc (S) (K) - Sum_Acc_Rev (S) (K)) >=
               abs (Sum_Acc (S) (Index) - Sum_Acc_Rev (S) (Index))));
     end loop;
     return Index;
  end Find_Fulcrum;

end Fulcrum;
