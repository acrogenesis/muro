defmodule Muro.PrintTest do
  use ExUnit.Case, async: true

  alias Muro.Print

  test "offset_to_loc is 1-based line and column" do
    src = "ab\ncd"
    assert Print.offset_to_loc(src, 0) == {1, 1}
    assert Print.offset_to_loc(src, 2) == {1, 3}
    assert Print.offset_to_loc(src, 3) == {2, 1}
  end

  test "offset_to_loc keeps a trailing newline on the last line" do
    src = "ab\n\nc"
    assert Print.offset_to_loc(src, 3) == {2, 1}
    assert Print.offset_to_loc(src, 4) == {3, 1}
    assert Print.offset_to_loc(src, byte_size(src)) == {3, 2}
    src = "ab\n"
    assert Print.offset_to_loc(src, byte_size(src)) == {1, 3}
    assert Print.offset_to_loc("", 0) == {1, 1}
  end

  test "term prints binders and free variables by name" do
    names = ["n"]
    ty = {:idt, :nat, {:var, 0}, :ze}
    assert Print.term(ty, names) == "{n ≡ 0 : Nat}"
    assert Print.term({:pi, :affine, :nat, "n", {:var, 0}}, []) == "Π (n : Nat) → n"
  end

  test "hole_message lists the context oldest first" do
    gamma = [{:affine, :nat}]
    msg = Print.hole_message({2, 19}, gamma, ["n"], :nat)
    assert msg =~ "2:19: unsolved hole"
    assert msg =~ "expected: Nat"
    assert msg =~ "n : Nat"
  end
end
