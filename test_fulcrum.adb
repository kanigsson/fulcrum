with Ada.Text_IO;
with Fulcrum; use Fulcrum;

procedure Test_Fulcrum is
  A : Seq := (5,5,10);
  B : Seq := (1,2,3,4,5,6);
begin
   pragma Assert (Find_Fulcrum (A) = 2);
   pragma Assert (Find_Fulcrum (B) = 2);
end Test_Fulcrum;
