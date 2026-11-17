defmodule MuroPrefixTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Parser}

  @proto """
  data Piece : Type where
    piece-chunk : Piece
    piece-req : Piece

  data Reply : Type where
    reply-ok : Reply
    reply-bad : Reply

  session ack := send Bit end

  session conn :=
    rec Loop.
      choose
        (recv (p : Piece)
          (case p
            | piece-chunk => Loop
            | piece-req => send Reply (choose Loop ack)))
        end

  session peer := dual conn
  """

  test "the example book checks, including a prefix from the reply state" do
    path = "examples/prefix.muro"
    assert Muro.check_file(path) == :ok

    {:ok, book} = Parser.parse(File.read!(path))
    {:ok, %{nodes: nodes}} = Muro.Emit.C.Session.positions(book, path)

    id =
      Enum.find_value(nodes, fn {id, node} ->
        if node.session == "conn" and String.contains?(node.step, "send Reply"), do: id
      end)

    assert id == 5
    assert File.read!(path) =~ "prefix at-reply : conn at #{id} :="
  end

  test "a multi-move prefix and a prefix from the middle both check" do
    assert check(
             @proto <>
               """
               prefix admit : conn :=
                 send pick b0
                 recv piece-req
                 send reply-bad
                 send pick b1
                 send b0

               prefix at-ack : conn at ack :=
                 send b0

               prefix at-loop : conn at Loop :=
                 send pick b1

               prefix empty : conn :=

               prefix named-start : conn at start :=
                 send pick b1
               """
           ) == :ok
  end

  test "a prefix from the reply state is a legal continuation" do
    {id, _} = reply_node()

    assert check(
             @proto <>
               """
               prefix at-reply : conn at #{id} :=
                 send reply-ok
                 send pick b0
               """
           ) == :ok
  end

  test "the wrong direction is refused" do
    assert {:error, msg} =
             check(
               @proto <>
                 """
                 prefix wrong : conn :=
                   recv pick b0
                 """
             )

    assert msg =~
             "wrong: move 1 has the wrong direction: expected send pick, wrote recv pick b0"
  end

  test "an unknown constructor is refused" do
    assert {:error, msg} =
             check(
               @proto <>
                 """
                 prefix bad-ctor : conn :=
                   send pick b0
                   recv nope
                 """
             )

    assert msg =~
             "bad-ctor: move 2 is not a legal continuation of conn at start: unknown constructor nope of Piece"
  end

  test "a move the position does not allow is refused" do
    {id, _} = reply_node()

    assert {:error, msg} =
             check(
               @proto <>
                 """
                 prefix idle : conn at #{id} :=
                   send pick b0
                 """
             )

    assert msg =~
             "idle: not enabled at #{id}, expected send Reply, wrote send pick b0"

    refute msg =~ "wrong direction"
  end

  test "a later move that is not a legal continuation is refused" do
    {id, _} = reply_node()

    assert {:error, msg} =
             check(
               @proto <>
                 """
                 prefix later : conn at #{id} :=
                   send reply-ok
                   recv piece-req
                 """
             )

    assert msg =~
             "later: move 2 is not a legal continuation of conn at #{id}: has the wrong direction: expected send pick, wrote recv piece-req"
  end

  test "zero and another session's state are not positions" do
    assert {:error, msg} =
             check(
               @proto <>
                 """
                 prefix zero : conn at 0 :=
                 """
             )

    assert msg =~ "zero: at 0 is not a position of conn"

    {:ok, book} = Parser.parse(@proto)
    {:ok, %{nodes: nodes}} = Muro.Emit.C.Session.positions(book, "prefix.muro")
    {ack_id, _} = Enum.find(nodes, fn {_id, node} -> node.session == "ack" end)

    assert {:error, other} =
             check(
               @proto <>
                 """
                 prefix borrowed : conn at #{ack_id} :=
                   send b0
                 """
             )

    assert other =~ "borrowed: at #{ack_id} is not a position of conn"
  end

  test "an evidence bound accepts a numeral inside it and refuses one outside it" do
    src = """
    session win := send (d : Nat) {d ≤ 3} end

    prefix fits : win :=
      send 2
    """

    assert check(src) == :ok

    assert {:error, msg} =
             check(
               src <>
                 """
                 prefix over : win :=
                   send 4
                 """
             )

    assert msg =~ "over: not enabled at start"
    assert msg =~ "wrote send 4"
    refute msg =~ "unknown constructor"
  end

  test "a bound that is not a numeral is not known" do
    assert {:error, msg} =
             check("""
             session echo := recv (n : Nat) (send (d : Nat) {d ≤ n} end)

             prefix open : echo :=
               recv 1
               send 0
             """)

    assert msg =~
             "open: move 2 is not a legal continuation of echo at start: bound n is not known at start"
  end

  test "a case on a run is not a prefix step when a move remains" do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    def late : run Π (b : Bool) → Bool :=
      λ (b : Bool) →
        match b motive (λ _ → Bool)
          | true => true
          | false => false

    session gate :=
      recv (b : Bool) (case (late b)
        | true => end
        | false => end)

    prefix stop : gate :=
      recv true
    """

    assert check(src) == :ok

    assert {:error, msg} =
             check(
               src <>
                 """
                 prefix go : gate :=
                   recv true
                   send pick b0
                 """
             )

    assert msg =~ "case (late b) is not a prefix step"
  end

  test "prefix is a declaration word and still a legal definition name" do
    assert check("""
           def prefix : run Nat := 0
           def start : run Nat := 0
           def pick : run Nat := 0
           """) == :ok

    assert {:error, msg} =
             check("""
             session ack := send Bit end

             prefix admit : ack :=
               send b0

             def use : run Nat := admit
             """)

    assert msg =~ "admit is a prefix, not a definition"
  end

  test "dual of a session that continues is the other end" do
    assert check("""
           #{@proto}
           prefix dual-start : dual conn :=
             recv pick b1

           prefix dual-ack : dual conn at ack :=
             recv b0
           """) == :ok
  end

  test "dual of a dual session is that session at the continuation" do
    assert check("""
           #{@proto}
           prefix dual-peer-ack : dual peer at ack :=
             send b0
           """) == :ok

    assert {:error, msg} =
             check("""
             #{@proto}
             prefix dual-peer-ack : dual peer at ack :=
               recv b0
             """)

    assert msg =~ "has the wrong direction: expected send Bit, wrote recv b0"
  end

  test "a session argument stops before at, and dual of an applied session is a use" do
    assert check("""
           data Bool : Type where
             true : Bool
             false : Bool

           session flag (k : Nat) := send Bool end

           prefix one : flag 1 :=
             send true

           prefix there : flag 1 at start :=
             send false

           prefix back : dual (flag 1) :=
             recv true
           """) == :ok
  end

  defp reply_node do
    {:ok, book} = Parser.parse(@proto)
    {:ok, %{nodes: nodes}} = Muro.Emit.C.Session.positions(book, "prefix.muro")

    Enum.find(nodes, fn {_id, node} ->
      node.session == "conn" and String.contains?(node.step, "send Reply")
    end)
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end
