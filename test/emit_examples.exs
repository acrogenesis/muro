# The image of every example except the keyed family. `mix muro.emit`
# skips a family, so these bytes are the bytes main emitted. The digest
# is one sha256 per book. Keyed-slots is the book this change adds.
#
# An Elixir image is hashed as its parsed form. Elixir 1.20 prints a map
# in iterator order and breaks a line where 1.18 does not, and that order
# follows atoms already created in the VM. The parsed form is the image.
defmodule Muro.EmitExamples do
  @exclude "keyed-slots.muro"

  def lines(root \\ "examples") do
    root
    |> Path.join("**/*.muro")
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.reject(&String.ends_with?(&1, @exclude))
    |> Enum.map(fn path ->
      rel = Path.relative_to(path, root)
      if System.get_env("MURO_EMIT_DIGEST") == "1", do: IO.puts(:stderr, rel)
      hash = path |> picture() |> canon() |> :erlang.term_to_binary([:deterministic]) |> sha()
      "#{hash}  #{rel}"
    end)
  end

  def picture(path) do
    stem = Path.basename(path, ".muro")
    closed = load(path, [])
    opened = load(path, params: :open)
    book = erased(closed)

    %{
      elixir: attempt(fn -> elixir(book, path) end),
      c: attempt(fn -> stem_render(&Muro.Emit.C.prepare/2, book, stem) end),
      rust: attempt(fn -> stem_render(&Muro.Emit.Rust.render/2, book, stem) end),
      zig: attempt(fn -> stem_render(&Muro.Emit.Zig.render/2, book, stem) end),
      asm: attempt(fn -> stem_render(&Muro.Emit.Asm.render/2, book, stem) end),
      js: attempt(fn -> js(book, stem, path) end),
      fsm: attempt(fn -> fsm(book, path) end),
      otp: attempt(fn -> stem_render(&Muro.Emit.Otp.render/2, book, stem) end),
      node: attempt(fn -> node(book, stem) end),
      mbi: attempt(fn -> mbi(closed) end),
      exunit: attempt(fn -> exunit(opened, path) end)
    }
  end

  defp load(path, opts) do
    case Muro.Load.file(path, opts) do
      {:ok, book} -> {:ok, book}
      {:error, msg} -> {:error, msg}
    end
  end

  defp erased({:ok, book}), do: {:ok, book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()}
  defp erased(other), do: other

  defp elixir({:error, msg}, _path), do: {:error, msg}

  defp elixir({:ok, book}, path) do
    case Muro.Emit.refuse_may_fail(book) do
      :ok -> {:ok, Muro.Emit.emit_module(Muro.Emit.elixir_module(path), book)}
      other -> other
    end
  end

  # C's prepare returns the header, the source, and the NIF signatures.
  # The signatures are not the file. The header and the source are.
  defp stem_render(_fun, {:error, msg}, _stem), do: {:error, msg}

  defp stem_render(fun, {:ok, book}, stem) do
    case fun.(book, stem) do
      {:ok, header, source, _sigs} -> {:ok, header, source}
      other -> other
    end
  end

  defp js({:error, msg}, _stem, _path), do: {:error, msg}
  defp js({:ok, book}, stem, path), do: Muro.Emit.JS.render(book, stem, path: path)

  defp fsm({:error, msg}, _path), do: {:error, msg}

  defp fsm({:ok, book}, path) do
    Muro.Emit.Fsm.render(book, path, Muro.Emit.fsm_module(path))
  end

  defp node({:error, msg}, _stem), do: {:error, msg}
  defp node({:ok, book}, stem), do: Muro.Emit.Node.render(book, stem, :a)

  defp mbi({:error, msg}), do: {:error, msg}
  defp mbi({:ok, book}), do: Muro.Emit.Mbi.render(Muro.Prelude.for_emit(book))

  defp exunit({:error, msg}, _path), do: {:error, msg}

  defp exunit({:ok, book}, path) do
    Muro.Emit.ExUnitSuite.render(path, Muro.Emit.exunit_module(path), Muro.Grade.erase_book(book))
  end

  defp attempt(fun) do
    try do
      norm(fun.())
    rescue
      e -> norm({:raise, e.__struct__, Exception.message(e)})
    catch
      kind, reason -> norm({:catch, kind, Exception.format(kind, reason, [])})
    end
  end

  defp norm(x) when is_binary(x) do
    cwd = File.cwd!()

    x
    |> String.replace(Path.expand(cwd), "")
    |> String.replace(cwd, "")
  end

  defp norm(x) when is_list(x), do: Enum.map(x, &norm/1)
  defp norm(x) when is_map(x), do: Map.new(x, fn {k, v} -> {norm(k), norm(v)} end)
  defp norm(x) when is_tuple(x), do: x |> Tuple.to_list() |> Enum.map(&norm/1) |> List.to_tuple()
  defp norm(x), do: x

  defp sha(bin), do: Base.encode16(:crypto.hash(:sha256, bin), case: :lower)

  defp canon(x) when is_binary(x) do
    if String.starts_with?(String.trim_leading(x), "defmodule ") do
      case Code.string_to_quoted(x, columns: false) do
        {:ok, ast} -> {:elixir, strip(ast)}
        _ -> x
      end
    else
      x
    end
  end

  defp canon(x) when is_list(x), do: Enum.map(x, &canon/1)
  defp canon(x) when is_map(x), do: Map.new(x, fn {k, v} -> {canon(k), canon(v)} end)

  defp canon(x) when is_tuple(x),
    do: x |> Tuple.to_list() |> Enum.map(&canon/1) |> List.to_tuple()

  defp canon(x), do: x

  # Drop parser metadata, and sort a map by its keys. Atom order in a VM
  # is not the order of the names, so the sort key is the external binary.
  defp strip({:%{}, meta, args}) when is_list(meta) do
    {base, pairs} =
      case args do
        [{:|, inner, [left, extra]}] when is_list(inner) and is_list(extra) ->
          {strip(left), extra}

        pairs when is_list(pairs) ->
          {nil, pairs}
      end

    pairs =
      pairs
      |> Enum.map(fn {k, v} -> {strip(k), strip(v)} end)
      |> Enum.sort_by(fn {k, _} -> :erlang.term_to_binary(k, [:deterministic]) end)

    if base, do: {:map, base, pairs}, else: {:map, pairs}
  end

  defp strip({form, meta, args}) when is_list(meta) and is_list(args) do
    {strip(form), Enum.map(args, &strip/1)}
  end

  defp strip({form, meta, ctx}) when is_list(meta) and is_atom(ctx) do
    {strip(form), ctx}
  end

  defp strip({a, b}), do: {strip(a), strip(b)}
  defp strip(list) when is_list(list), do: Enum.map(list, &strip/1)
  defp strip(other), do: other
end

if System.get_env("MURO_EMIT_DIGEST") == "1" do
  IO.puts(Enum.join(Muro.EmitExamples.lines(), "\n"))
end
