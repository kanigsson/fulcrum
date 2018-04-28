with Ada.Text_IO;
with Fulcrum; use Fulcrum;

procedure Test_Fulcrum is
  A : Seq := (5,5,10);
  B : Seq := (1,2,3,4,5,-7);
begin
   Ada.Text_IO.Put_Line (Find_Fulcrum (A)'Img);
   Ada.Text_IO.Put_Line (Find_Fulcrum (B)'Img);
end Test_Fulcrum;
