package body Fulcrum with SPARK_Mode is

   procedure Lemma_Safe_Sum_Left_Incr (S : Seq; A, B : Natural) is
   begin
      if A + 1 < B then
         Lemma_Safe_Sum_Left_Incr (S, A, B - 1);
         pragma Assert (Safe_Sum (S, A + 1, B).Kind = O_Some);
      else
         pragma Assert (Safe_Sum (S, A + 1, B).Kind = O_Some);
      end if;
   end Lemma_Safe_Sum_Left_Incr;


   procedure Lemma_Left_Incr (S : Seq; A, B : Natural) is
   begin
      if A + 1 < B then
         Lemma_Left_Incr (S, A, B - 1);
      end if;
   end Lemma_Left_Incr;
   --
   --
   --  --  Finally the implementation of Find_Fulcrum. It uses two variables
   --  --  Left_Sum and Right_Sum which contain the current values for those
   --  --  partial sums, as well as the variable Min for the current minimal
   --  --  difference between the sum, and the variable Index for the
   --  --  corresponding index.
   --  function Find_Fulcrum (S : Seq) return Opt_Nat is
   --     --  We initialize those four local variables, basically setting the
   --     --  current best index at the first cell of the array.
   --     Index : Natural := S'First;
   --     --  The first partial sum from the left is just the first cell of the
   --     --  array.
   --     Left_Sum : Natural := S'First;
   --     --  The first partial sum from the right uses the Sum function. We need
   --     --  to exclude the first value so that Right_Sum corresponds to the sum
   --     --  excluding the first index.
   --     --  This is O(n) time, O(1) space.
   --     Right_Sum_Opt : constant Opt_Nat := Sum (S, S'First + 1, S'Last);
   --     --  The current best difference is just the first such difference.
   --     Right_Sum : Natural;
   --     Min : Natural;
   --  begin
   --     if Right_Sum_Opt.Kind = O_None then
   --        return (Kind => O_None);
   --     end if;
   --     Right_Sum := Right_Sum.Value;
   --     Min := abs (Left_Sum - Right_Sum);
   --     --  The code is now very straightforward. We iterate over the remainder
   --     --  of the array, adding the current value to the Left_Sum, and removing
   --     --  it from Right_Sum. We then compare their difference with the current
   --     --  best value Min, and update Min and Index if we found a new best
   --     --  value. This is clearly O(n) time. We don't do any calls or creation
   --     --  of new variables, so we stay at O(1) space.
   --     for I in S'First + 1 .. S'Last loop
   --        --  The loop invariants clearly express the intent of the four
   --        --  variables
   --        pragma Loop_Invariant
   --        --  We define what Left_Sum and Right_Sum are supposed to mean.
   --          (Left_Sum = Sum (S, S'First, I - 1).Value and then
   --           Right_Sum = Sum (S, I, S'Last).Value and then
   --             --  need to state that the Index variable is in range to be able to
   --           --  prove that the array accesses are within bounds
   --           Index in S'Range and then
   --           --  The link between Min and Index: Min contains the absolute
   --           --  difference between the partial sums at Index.
   --           Min = Diff_Sum (S, Index) and then
   --             --   and this is the best such difference up to now
   --             (for all K in S'First .. I - 1 => Diff_Sum (S, K) >= Min));
   --        if Left_Sum.Kind = O_None or else Right_Sum.Kind = O_None then
   --           return (Kind => O_None);
   --        end if;
   --        Left_Sum := Safe_Add (Left_Sum, S (I));
   --        Right_Sum := (O_Some, Right_Sum.Value - S (I));
   --        if Min >= Safe_Diff_Abs (Left_Sum, Right_Sum) then
   --           Min := Safe_Diff_Abs (Left_Sum, Right_Sum);
   --           Index := I;
   --        end if;
   --     end loop;
   --     return (O_Some, Index);
   --  end Find_Fulcrum;

end Fulcrum;
