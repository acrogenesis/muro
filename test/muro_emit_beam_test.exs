defmodule Muro.EmitBeamTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.Emit.Beam

  @images ~w(once affine reuse drop app suc match pi iv)

  @failures ~w(
    fail-typ fail-nat fail-unit fail-empty fail-data fail-id fail-def
    fail-pair fail-stream fail-machine fail-word
  )

  test "Agda agree strings are the Elixir images and the golden files" do
    agreed = agreements()

    for name <- @images do
      assert Map.has_key?(agreed, name), "missing agree:#{name}"
    end

    for name <- @failures do
      assert Map.has_key?(agreed, name), "missing agree:#{name}"
    end

    assert Beam.show_pure({:glam, 1, 0, {:gvar, 0}}) == agreed["once"]
    assert Beam.show_pure({:glam, {:iv, 0, 1}, 0, {:gvar, 0}}) == agreed["affine"]
    assert Beam.show_pure({:glam, :w, 0, {:gvar, 0}}) == agreed["reuse"]
    assert Beam.show_pure({:glam, 0, 0, :gze}) == agreed["drop"]
    assert Beam.show_pure({:gapp, {:glam, {:iv, 0, 1}, 0, {:gvar, 0}}, :gze}) == agreed["app"]
    assert Beam.show_pure({:gsu, {:gsu, :gze}}) == agreed["suc"]
    assert Beam.show_pure({:gmatch, :gze, :gze, {:gvar, 0}}) == agreed["match"]
    assert Beam.show_pure({:gpi, {:iv, 0, 1}, 0, {:gvar, 0}}) == agreed["pi"]
    assert Beam.show_pure({:glam, {:iv, 0, 2}, 0, {:gvar, 0}}) == agreed["iv"]

    for name <- ~w(once affine reuse drop app suc match) do
      assert File.read!("examples/images/#{name}.mbi") == agreed[name] <> "\n"
    end
  end

  test "erase agrees with the Agda strings on the shared terms" do
    agreed = agreements()

    assert shown({:lam, :linear, :nat, "n", {:var, 0}}) == agreed["once"]
    assert shown({:lam, {:grade, 1, 0}, :nat, "n", {:var, 0}}) == agreed["once"]
    assert shown({:lam, :affine, :nat, "n", {:var, 0}}) == agreed["affine"]
    assert shown({:lam, :reuse, :nat, "n", {:var, 0}}) == agreed["reuse"]
    assert shown({:lam, :reuse, :nat, "n", {:app, {:var, 0}, {:var, 0}}}) == agreed["twice"]
    assert shown({:lam, :erased, :nat, "n", :ze}) == agreed["drop"]
    assert shown({:app, {:lam, :affine, :nat, "n", {:var, 0}}, :ze}) == agreed["app"]
    assert shown({:su, {:su, :ze}}) == agreed["suc"]
    assert shown({:nat, 2}) == agreed["suc"]

    assert shown({:mnat, :ze, {:lam, :affine, :nat, "_", :nat}, :ze, {:var, 0}}) ==
             agreed["match"]

    assert shown({:pi, :affine, :nat, "n", {:var, 0}}) == agreed["pi"]
    assert shown({:lam, {:grade, {:iv, 0, 2}, 0}, :nat, "n", {:var, 0}}) == agreed["iv"]
    assert shown({:lam, :nope, :nat, "n", {:var, 0}}) == agreed["affine"]

    assert Beam.erase(:typ) == {:error, agreed["fail-typ"]}
    assert Beam.erase(:nat) == {:error, agreed["fail-nat"]}
    assert Beam.erase(:unit) == {:error, agreed["fail-unit"]}
    assert Beam.erase(:one) == {:error, agreed["fail-unit"]}
    assert Beam.erase({:munit, :ze, :ze, :ze}) == {:error, agreed["fail-unit"]}
    assert Beam.erase(:empty) == {:error, agreed["fail-empty"]}
    assert Beam.erase({:memp, :ze, :ze}) == {:error, agreed["fail-empty"]}
    assert Beam.erase({:mdata, :ze, :ze, []}) == {:error, agreed["fail-data"]}
    assert Beam.erase({:mwbool, :ze, :ze, []}) == {:error, agreed["fail-data"]}
    assert Beam.erase({:mopt, :ze, :ze, []}) == {:error, agreed["fail-data"]}
    assert Beam.erase(:rfl) == {:error, agreed["fail-id"]}
    assert Beam.erase({:idt, :nat, :ze, :ze}) == {:error, agreed["fail-id"]}
    assert Beam.erase({:rwt, :ze, :ze, :ze}) == {:error, agreed["fail-id"]}
    assert Beam.erase({:def, 0}) == {:error, agreed["fail-def"]}
    assert Beam.erase({:def, "plus"}) == {:error, agreed["fail-def"]}
    assert Beam.erase({:pair, :ze, :ze}) == {:error, agreed["fail-pair"]}
    assert Beam.erase({:prod, :nat, :nat}) == {:error, agreed["fail-pair"]}
    assert Beam.erase({:letp, :ze, :ze}) == {:error, agreed["fail-pair"]}
    assert Beam.erase({:nu, :ze}) == {:error, agreed["fail-stream"]}
    assert Beam.erase({:unf, {:pair, :ze, :ze}, :ze}) == {:error, agreed["fail-stream"]}
    assert Beam.erase({:ucons, :ze}) == {:error, agreed["fail-stream"]}
    assert Beam.erase({:bisim, :ze, :ze}) == {:error, agreed["fail-stream"]}
    assert Beam.erase({:stream, :nat}) == {:error, agreed["fail-stream"]}
    assert Beam.erase({:always, :nat, :ze, :ze}) == {:error, agreed["fail-stream"]}
    assert Beam.erase(:i64) == {:error, agreed["fail-machine"]}
    assert Beam.erase(:f32ty) == {:error, agreed["fail-machine"]}
    assert Beam.erase({:tensor, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Beam.erase({:addi, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Beam.erase({:muli, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Beam.erase({:addt, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Beam.erase({:toi64, :ze}) == {:error, agreed["fail-machine"]}
    assert Beam.erase({:packi, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Beam.erase({:word, :add, []}) == {:error, agreed["fail-word"]}
  end

  test "every Elixir-only refusal is named, and a bad numeral is not a successor" do
    assert Beam.erase(:string) == {:error, "string"}
    assert Beam.erase({:slit, "hi"}) == {:error, "string"}
    assert Beam.erase({:scat, :ze, :ze}) == {:error, "string"}
    assert Beam.erase({:slen, :ze}) == {:error, "string"}
    assert Beam.erase({:seq, :ze, :ze}) == {:error, "string"}
    assert Beam.erase(:bytes) == {:error, "bytes"}
    assert Beam.erase(:slice) == {:error, "bytes"}
    assert Beam.erase({:blit, "hi"}) == {:error, "bytes"}
    assert Beam.erase({:bcat, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:blen, :ze}) == {:error, "bytes"}
    assert Beam.erase({:beq, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:xlen, :ze}) == {:error, "bytes"}
    assert Beam.erase({:xeq, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:bsub, :ze, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:bget, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:aget, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:bunc, :ze}) == {:error, "bytes"}
    assert Beam.erase({:bfold, :ze, :ze, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:afold, :ze, :ze, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:sbytes, :ze}) == {:error, "bytes"}
    assert Beam.erase({:btil, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase({:baft, :ze, :ze}) == {:error, "bytes"}
    assert Beam.erase(:atom) == {:error, "atom"}
    assert Beam.erase({:atom, "hello"}) == {:error, "atom"}
    assert Beam.erase({:matom, :ze, :ze, []}) == {:error, "atom"}
    assert Beam.erase({:hole, nil}) == {:error, "hole"}
    assert Beam.erase({:nat, -1}) == {:error, "numeral"}
    assert Beam.erase({:nat, 1.5}) == {:error, "numeral"}
    assert Beam.erase({:lam, {:grade, :nope, 0}, :nat, "n", :ze}) == {:error, "grade"}
    assert Beam.erase({:lam, {:grade, {:iv, :nope, 1}, 0}, :nat, "n", :ze}) == {:error, "grade"}
    assert Beam.erase(:nope) == {:error, "term"}
    assert Beam.show_grade(:w) == "w"
    assert Beam.show_grade(10) == "10"
    assert Beam.erase({:ann, :ze, :nat}) == {:ok, :gze}
  end

  test "a checked book writes the golden image" do
    assert emit_src(affine_src()) == golden("affine")
    assert emit_src(percent_zero_src()) == golden("affine")
    assert emit_src(app_src()) == golden("app")
    assert emit_src(suc_src()) == golden("suc")
    assert emit_src(numeral_src()) == golden("suc")
    assert emit_src(match_src()) == golden("match")
    assert emit_src(drop_src()) == golden("drop")
    assert emit_src(reuse_src()) == golden("reuse")
    assert emit_src(linear_src()) == golden("once")
    assert emit_src(interval_src()) == agreements()["iv"] <> "\n"

    dir = tmp_dir()
    path = write_book(dir, "keep", data_and_zero_src())
    assert {:ok, [file]} = Muro.emit_beam(path)
    assert File.read!(file) == Beam.show_pure(:gze) <> "\n"

    path = write_book(dir, "both", spec_and_zero_src())
    assert {:ok, [file]} = Muro.emit_beam(path)
    assert File.read!(file) == Beam.show_pure(:gze) <> "\n"

    path = write_book(dir, "hid", internal_and_zero_src())
    assert {:ok, [file]} = Muro.emit_beam(path)
    assert File.read!(file) == Beam.show_pure(:gze) <> "\n"
  end

  test "grades.muro writes once and refuses many" do
    dir = tmp_dir()
    path = Path.join(dir, "grades.muro")
    File.cp!("examples/grades.muro", path)
    file = Path.join(dir, "grades.mbi")

    out =
      capture_io(fn ->
        assert_raise Mix.Error, ~r/\Abeam:def in many\z/, fn ->
          Mix.Tasks.Muro.Emit.run([path, "--backend", "beam"])
        end
      end)

    assert out == file <> "\n"
    assert File.read!(file) == golden("once")
    assert {:error, "beam:def in many"} = Muro.emit_beam(path)
  end

  test "a later run is named, an earlier failure keeps its reason, and a miss writes nothing" do
    dir = tmp_dir()

    path = write_book(dir, "two", two_src())
    assert {:error, "beam:entry in b"} = Muro.emit_beam(path)
    assert File.read!(Path.join(dir, "two.mbi")) == Beam.show_pure(:gze) <> "\n"

    path = write_book(dir, "repair", repair_src())
    assert {:error, "beam:pair in bad"} = Muro.emit_beam(path)
    assert File.read!(Path.join(dir, "repair.mbi")) == Beam.show_pure(:gze) <> "\n"

    path = write_book(dir, "none", "def p : spec Nat := 0\n")
    File.write!(Path.join(dir, "none.mbi"), "stale\n")
    assert {:error, "beam:entry"} = Muro.emit_beam(path)
    refute File.exists?(Path.join(dir, "none.mbi"))

    path = write_book(dir, "hid", "def hidden : run internal Nat := 0\n")
    assert {:error, "beam:entry"} = Muro.emit_beam(path)
    refute File.exists?(Path.join(dir, "hid.mbi"))

    path = write_book(dir, "data", data_match_src())
    assert {:error, "beam:data in n"} = Muro.emit_beam(path)
    refute File.exists?(Path.join(dir, "data.mbi"))

    path = write_book(dir, "str", "def hello : run String := \"hello\"\n")
    assert {:error, "beam:string in hello"} = Muro.emit_beam(path)

    path = write_book(dir, "oct", "def hello : run Bytes := b\"hello\"\n")
    assert {:error, "beam:bytes in hello"} = Muro.emit_beam(path)

    path = write_book(dir, "tag", "def tag : run Atom := :hello\n")
    assert {:error, "beam:atom in tag"} = Muro.emit_beam(path)

    path = write_book(dir, "zeros", zeros_src())
    assert {:error, "beam:stream in zeros"} = Muro.emit_beam(path)

    src = File.read!("examples/internal_ok.muro")
    path = write_book(dir, "internal_ok", src)
    assert {:error, "beam:def in inc"} = Muro.emit_beam(path)
    refute File.exists?(Path.join(dir, "internal_ok.mbi"))

    assert {:error, "beam:term in bad"} =
             Beam.render([%{name: "bad", mode: :run, type: :nat, body: {:nope}}])

    assert {:error, "beam:entry"} = Beam.render([])
  end

  test "the mix task prints the path, and node and imports are refused before a file" do
    dir = tmp_dir()
    path = write_book(dir, "id", affine_src())

    assert capture_io(fn ->
             Mix.Tasks.Muro.Emit.run([path, "--backend", "beam"])
           end) == Path.join(dir, "id.mbi") <> "\n"

    assert {:ok, out, ""} = Muro.CLI.Emit.run([path, "--backend", "beam"])
    assert out == Path.join(dir, "id.mbi") <> "\n"

    assert {:raise, "", "--node writes the placement calls"} =
             Muro.CLI.Emit.run([path, "--backend", "beam", "--node", "a"])

    assert {:raise, "", "--imports is only valid with --backend exunit"} =
             Muro.CLI.Emit.run([path, "--backend", "beam", "--imports"])

    bad = write_book(dir, "bad", "def n : run Nat := (0, 0)\n")
    stale = Path.join(dir, "bad.mbi")
    File.write!(stale, "stale\n")

    assert {:raise, "", message} = Muro.CLI.Emit.run([bad, "--backend", "beam"])
    refute String.starts_with?(message, "beam:")
    assert File.read!(stale) == "stale\n"
  end

  defp shown(term) do
    assert {:ok, gtm} = Beam.erase(term)
    Beam.show_pure(gtm)
  end

  defp agreements do
    "agda/Muro/Beam.agda"
    |> File.read!()
    |> then(fn src ->
      Regex.scan(~r/-- agree:(\S+)\n[^\n]*≡ (?:fail )?"([^"]*)"/u, src)
    end)
    |> Map.new(fn [_, name, image] -> {name, image} end)
  end

  defp golden(name), do: File.read!("examples/images/#{name}.mbi")

  defp emit_src(src) do
    dir = tmp_dir()
    path = write_book(dir, "book", src)
    assert {:ok, [file]} = Muro.emit_beam(path)
    File.read!(file)
  end

  defp write_book(dir, name, src) do
    path = Path.join(dir, name <> ".muro")
    File.write!(path, src)
    path
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_beam_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp affine_src do
    """
    def id : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    """
  end

  defp percent_zero_src do
    """
    def id : run Π (%0 n : Nat) → Nat :=
      λ (%0 n : Nat) → n
    """
  end

  defp app_src do
    """
    def z : run Nat := (λ (n : Nat) → n) 0
    """
  end

  defp suc_src do
    """
    def two : run Nat := suc (suc 0)
    """
  end

  defp numeral_src do
    """
    def two : run Nat := 2
    """
  end

  defp match_src do
    """
    def pred0 : run Nat :=
      match 0 motive (λ _ → Nat)
        | 0 => 0
        | suc m => m
    """
  end

  defp drop_src do
    """
    def drop : run Π (- n : Nat) → Nat :=
      λ (- n : Nat) → 0
    """
  end

  defp reuse_src do
    """
    def id : run Π (+ n : Nat) → Nat :=
      λ (+ n : Nat) → n
    """
  end

  defp linear_src do
    """
    def id : run Π (%1 n : Nat) → Nat :=
      λ (%1 n : Nat) → n
    """
  end

  defp interval_src do
    """
    def id : run Π (n : ([0, 2], 0) Nat) → Nat :=
      λ (n : ([0, 2], 0) Nat) → n
    """
  end

  defp two_src do
    """
    def a : run Nat := 0
    def b : run Nat := suc 0
    """
  end

  defp repair_src do
    """
    def bad : run Nat × Nat := (0, 0)
    def good : run Nat := 0
    """
  end

  defp data_and_zero_src do
    """
    data Bool : Type where
      tt : Bool
      ff : Bool

    def z : run Nat := 0
    """
  end

  defp data_match_src do
    """
    data Bool : Type where
      tt : Bool
      ff : Bool

    def n : run Π (b : Bool) → Nat :=
      λ (b : Bool) →
        match b motive (λ _ → Nat)
          | tt => 0
          | ff => 0
    """
  end

  defp spec_and_zero_src do
    """
    def p : spec Nat := 0
    def z : run Nat := 0
    """
  end

  defp internal_and_zero_src do
    """
    def hidden : run internal Nat := 0
    def z : run Nat := 0
    """
  end

  defp zeros_src do
    """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def zeros : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))
    """
  end
end
