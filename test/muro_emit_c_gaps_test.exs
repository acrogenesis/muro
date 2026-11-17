defmodule Muro.EmitCGapsTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  # The host program below is the muro-http shape: two books in one
  # translation unit, a constructor word instead of a tag-to-string map,
  # the named stepper constants, and an I64 of −1. A second session book
  # is prefixed so its entry points link beside the first.

  @conn """
  data Piece : Type where
    piece-chunk : Piece
    piece-req : Piece
    piece-bad : Piece

  data Reply : Type where
    reply-ok : Reply
    reply-bad : Reply

  session conn := recv Piece (send Reply end)
  """

  @peer """
  session peer := recv Nat end
  """

  @wide """
  session wide (a : Nat) (b : Nat) := send Nat end
  """

  @plain """
  def n : run Nat := 0
  """

  @sent """
  def neg : run I64 := subi (toI64 0) (toI64 1)

  def below : run Π (status : I64) → Nat :=
    λ (status : I64) →
      match (lti status (toI64 0)) motive (λ _ → Nat)
        | wtrue => suc 0
        | wfalse => 0
  """

  @left """
  def mark : run internal Nat := 0
  def seen : run Nat := mark
  """

  @right """
  def mark : run internal Nat := suc 0
  def other : run Nat := mark
  """

  @hook_zero """
  def mark : run internal Nat := 0
  def hook : run Nat := 0
  """

  @hook_one """
  def mark : run internal Nat := suc 0
  def hook : run Nat := suc 0
  """

  @id """
  data Path : Type where
    path-health : Path
    path-bad : Path
    path-id : Path

  data IdClass : Type where
    id-none : IdClass
    id-bad : IdClass
    id-unknown : IdClass
    id-missing : IdClass
    id-present : IdClass

  def pathOf : run Π (n : Nat) → Path :=
    λ (n : Nat) →
      match n motive (λ _ → Path)
        | 0 => path-health
        | suc k =>
            match k motive (λ _ → Path)
              | 0 => path-bad
              | suc _ => path-id

  def idClassOf : run Π (n : Nat) → IdClass :=
    λ (n : Nat) →
      match (pathOf n) motive (λ _ → IdClass)
        | path-health => id-none
        | path-bad => id-bad
        | path-id => id-unknown

  def idFrom : run Π (n : Nat) → IdClass :=
    λ (n : Nat) →
      match n motive (λ _ → IdClass)
        | 0 => id-missing
        | suc _ => id-present

  def idNumber : run Π (n : Nat) → I64 :=
    λ (n : Nat) →
      match (idClassOf n) motive (λ _ → I64)
        | id-none => toI64 0
        | id-bad => toI64 0
        | id-unknown => toI64 1
        | id-missing => toI64 0
        | id-present => toI64 0

  def idCount : run Π (n : Nat) → I64 :=
    λ (n : Nat) →
      match (idFrom n) motive (λ _ → I64)
        | id-none => toI64 0
        | id-bad => toI64 0
        | id-unknown => toI64 0
        | id-missing => toI64 2
        | id-present => toI64 3

  def idTag : run Π (i : IdClass) → Nat :=
    λ (i : IdClass) →
      match i motive (λ _ → Nat)
        | id-none => 0
        | id-bad => suc 0
        | id-unknown => suc (suc 0)
        | id-missing => suc (suc (suc 0))
        | id-present => suc (suc (suc (suc 0)))
  """

  test "a word step, named enums, a signed sentinel, and two headers compile together" do
    dir = tmp_dir()
    {conn_h, _conn_c} = emit!(dir, "conn", @conn)
    {peer_h, _peer_c} = emit!(dir, "peer", @peer, c_prefix: "p_")
    {_plain_h, _plain_c} = emit!(dir, "plain", @plain)
    {_sent_h, _sent_c} = emit!(dir, "sent", @sent)
    {left_h, left_c} = emit!(dir, "left", @left)
    {_right_h, _right_c} = emit!(dir, "right", @right)
    {zero_h, zero_c} = emit!(dir, "ha", @hook_zero, c_prefix: "a_")
    {_one_h, _one_c} = emit!(dir, "hb", @hook_one, c_prefix: "b_")

    chunk = Muro.Emit.C.ctor_word("conn", "Piece", "piece-chunk")
    reply_ok = Muro.Emit.C.ctor_word("conn", "Reply", "reply-ok")
    reply_bad = Muro.Emit.C.ctor_word("conn", "Reply", "reply-bad")
    reply_tag = Muro.Emit.C.ctor_tag("Reply", "reply-ok")

    assert conn_h =~ "#ifndef MURO__PRELUDE"
    assert conn_h =~ "typedef enum muro__sess_dir"
    assert conn_h =~ "MURO_SESS_SEND = 1"
    assert conn_h =~ "MURO_SESS_RECV = 2"
    assert conn_h =~ "MURO_SESS_PICK = 4"
    assert conn_h =~ "MURO_SESS_DATA = 8"
    assert conn_h =~ "muro__sess_conn_step("
    assert conn_h =~ "muro__sess_conn_step_word("
    assert conn_h =~ "#{chunk} = 0"
    assert conn_h =~ "#{reply_ok} = 3"
    assert conn_h =~ "#{reply_bad} = 4"
    assert conn_h =~ "#{reply_tag} = 0"
    assert conn_h =~ "#define MURO__SESS_SLOTS 1"
    assert peer_h =~ "#define MURO__SESS_SLOTS 1"
    assert peer_h =~ "p_muro__sess_peer_step_word("
    assert peer_h =~ "p_muro__sess_step_word("

    refute left_h =~ "mark("
    assert left_c =~ "__attribute__((unused)) static "
    assert left_c =~ "mark("
    assert zero_h =~ "a_hook("
    refute zero_h =~ "a_mark("
    refute zero_h =~ "mark("
    assert zero_c =~ "static "
    assert zero_c =~ "a_mark("

    File.write!(Path.join(dir, "main.c"), """
    #include "plain.h"
    #include "conn.h"
    #include "peer.h"
    #include "sent.h"
    #include "left.h"
    #include "right.h"
    #include "ha.h"
    #include "hb.h"
    #include <stdio.h>
    #include <string.h>

    _Static_assert(MURO_SESS_SEND == 1, "send");
    _Static_assert(MURO_SESS_RECV == 2, "recv");
    _Static_assert(MURO_SESS_PICK == 4, "pick");
    _Static_assert(MURO_SESS_DATA == 8, "data");
    _Static_assert(#{reply_tag} == 0, "reply tag");
    _Static_assert(#{chunk} == 0, "chunk word");
    _Static_assert(#{reply_ok} == 3, "reply-ok word");
    _Static_assert(#{reply_bad} == 4, "reply-bad word");

    int main(void) {
      muro__sess_res r = muro__sess_conn_init();
      if (r.status != MURO_SESS_OK) return 1;
      r = muro__sess_conn_step_word(r.state, MURO_SESS_RECV, MURO_SESS_DATA, #{chunk});
      if (r.status != MURO_SESS_OK || r.done) return 2;
      {
        muro__sess_res bad = muro__sess_conn_init();
        bad = muro__sess_conn_step_word(bad.state, MURO_SESS_RECV, MURO_SESS_DATA, 99);
        if (bad.status != MURO_SESS_UNEXPECTED) return 3;
      }
      {
        muro__sess_val ev;
        memset(&ev, 0, sizeof ev);
        ev.tag = MURO_SESS_DATA;
        ev.ctor = "reply-ok";
        r = muro__sess_conn_step(r.state, MURO_SESS_SEND, &ev);
        if (r.status != MURO_SESS_OK || !r.done) return 4;
      }
      {
        muro__sess_res p = p_muro__sess_peer_init();
        if (p.status != MURO_SESS_OK) return 5;
      }
      if (neg() != (int64_t)-1) return 6;
      if (below((int64_t)-1)->muro__field_tag != 1) return 7;
      if (below((int64_t)0)->muro__field_tag != 0) return 8;
      if (below((int64_t)1)->muro__field_tag != 0) return 9;
      if (n()->muro__field_tag != 0) return 10;
      if (seen()->muro__field_tag != 0) return 11;
      if (other()->muro__field_tag != 1) return 12;
      if (a_hook()->muro__field_tag != 0) return 13;
      if (b_hook()->muro__field_tag != 1) return 14;
      printf("ok\\n");
      return 0;
    }
    """)

    for stem <- ~w(conn peer plain sent left right ha hb main) do
      cc!(dir, "#{stem}.c", "#{stem}.o")
    end

    out = link!(dir, ~w(conn peer plain sent left right ha hb main))
    assert out == "ok\n"
  end

  test "two session headers with different nat-slot counts do not compile together" do
    dir = tmp_dir()
    emit!(dir, "conn", @conn)
    {wide_h, _} = emit!(dir, "wide", @wide)
    assert wide_h =~ "#define MURO__SESS_SLOTS 2"

    File.write!(Path.join(dir, "clash.c"), """
    #include "conn.h"
    #include "wide.h"
    """)

    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11 -c clash.c -o clash.o),
        cd: dir,
        stderr_to_stdout: true
      )

    assert status != 0
    assert out =~ "muro session state slot count differs between headers"
  end

  test "a prefix that is not a C identifier is refused, and elixir refuses the flag" do
    dir = tmp_dir()
    path = Path.join(dir, "plain.muro")
    File.write!(path, @plain)
    {:ok, book} = Muro.Load.file(path)
    book = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()

    assert {:error, "c:prefix"} =
             Muro.Emit.C.prepare(book, "plain", path: path, c_prefix: "1bad")

    assert {:error, "c:prefix"} =
             Muro.Emit.C.prepare(book, "plain", path: path, c_prefix: "admit-")

    assert {:ok, header, _source, sigs} =
             Muro.Emit.C.prepare(book, "plain", path: path, c_prefix: "admit_")

    assert header =~ "admit_n("
    assert Enum.map(sigs, & &1.name) == ["admit_n"]

    assert {:raise, "", "--prefix is only valid with --backend c"} =
             Muro.CLI.Emit.run([path, "--prefix", "admit_"])

    assert {:raise, "", "c:prefix"} =
             Muro.CLI.Emit.run([path, "--backend", "c", "--prefix", "1bad"])
  end

  test "a manifest c_prefix reaches the committed C symbol" do
    dir = tmp_dir()
    File.mkdir_p!(Path.join(dir, "priv/muro"))
    File.write!(Path.join(dir, "priv/muro/one.muro"), "def one : run Nat := 0\n")
    version = Mix.Tasks.Muro.version()

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "#{version}",
      modules: [
        {"priv/muro/one.muro", "lib/one.c", [kind: :c, c_prefix: "admit_"]}
      ]
    ]
    """)

    File.cd!(dir, fn ->
      capture_io(fn -> assert Mix.Tasks.Muro.Gen.run([]) == :ok end)
    end)

    header = File.read!(Path.join(dir, "lib/one.h"))
    assert header =~ "admit_one("
    refute header =~ ~r/(^|[^*_])one\(/
  end

  test "unreachable id-missing and id-present clauses are omitted and the live ones run" do
    dir = tmp_dir()
    path = Path.join(dir, "id.muro")
    File.write!(path, @id)
    assert {:ok, source} = Muro.emit_file(path, CGapsId)

    number = fun_body!(source, "idNumber", "idCount")
    refute number =~ ":id_missing"
    refute number =~ ":id_present"
    assert number =~ ":id_none"
    assert number =~ ":id_bad"
    assert number =~ ":id_unknown"

    count = fun_body!(source, "idCount", "idTag")
    assert count =~ ":id_missing"
    assert count =~ ":id_present"
    refute count =~ ":id_none"
    refute count =~ ":id_bad"
    refute count =~ ":id_unknown"

    tag = fun_body!(source, "idTag", nil)

    for atom <- ~w(:id_none :id_bad :id_unknown :id_missing :id_present) do
      assert tag =~ atom
    end

    mod = compile_source!(source, CGapsId)
    assert mod.idClassOf(0) == :id_none
    assert mod.idClassOf({:suc, 0}) == :id_bad
    assert mod.idClassOf({:suc, {:suc, 0}}) == :id_unknown
    assert mod.idNumber(0) == 0
    assert mod.idNumber({:suc, 0}) == 0
    assert mod.idNumber({:suc, {:suc, 0}}) == 1
    assert mod.idCount(0) == 2
    assert mod.idCount({:suc, 0}) == 3
    assert mod.idTag(:id_missing) == {:suc, {:suc, {:suc, 0}}}
    assert mod.idTag(:id_present) == {:suc, {:suc, {:suc, {:suc, 0}}}}
  end

  defp fun_body!(source, name, next) do
    stop = if next, do: "\\n+\\s*def #{next}\\b", else: "(?:\\n+\\s*defp\\b|\\s*\\z)"
    regex = Regex.compile!("def #{name}\\(.*?\\n  end(?=#{stop})", "s")

    case Regex.run(regex, source) do
      [body] -> body
      _ -> flunk("no #{name} in\n#{source}")
    end
  end

  defp compile_source!(source, mod) do
    Code.compiler_options(ignore_module_conflict: true)

    {compiled, diagnostics} =
      Code.with_diagnostics(fn ->
        Code.compile_string(source)
      end)

    warnings = for %{severity: :warning, message: message} <- diagnostics, do: message

    if warnings != [] do
      flunk("generated #{inspect(mod)} warned:\n" <> Enum.join(warnings, "\n"))
    end

    [{^mod, _bin}] = compiled

    on_exit(fn ->
      :code.purge(mod)
      :code.delete(mod)
    end)

    mod
  end

  defp emit!(dir, stem, text, opts \\ []) do
    path = Path.join(dir, stem <> ".muro")
    File.write!(path, text)
    {:ok, book} = Muro.Load.file(path)
    book = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()

    assert {:ok, header, source, _sigs} =
             Muro.Emit.C.prepare(book, stem, [path: path] ++ opts)

    File.write!(Path.join(dir, stem <> ".h"), header)
    File.write!(Path.join(dir, stem <> ".c"), source)
    {header, source}
  end

  defp cc!(dir, src, obj) do
    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11 -c) ++ [src, "-o", obj],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
  end

  defp link!(dir, stems) do
    objs = Enum.map(stems, &"#{&1}.o")

    {link, status} =
      System.cmd("cc", objs ++ ["-o", "main_bin"], cd: dir, stderr_to_stdout: true)

    assert status == 0, link
    {out, status} = System.cmd(Path.join(dir, "main_bin"), [], stderr_to_stdout: true)
    assert status == 0, out
    out
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_c_gaps_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
