defmodule Muro.Emit.Mbi do
  @moduledoc """
  Erase one exported run to an .mbi image.

  The rules are `agda/Muro/Beam.agda`. A grade pair and the `%1` mark
  are not constructors of `Tm`, so this module reads them. Success is
  exactly one exported run. The image is text. muro-beam loads it and
  checks the term again. The file is not Erlang BEAM bytecode. Writing
  the image is not that check. See [MBI images](manual/mbi.md).
  """

  alias Muro.Ast

  @format_version 1
  @boundary_version 1

  @type point :: non_neg_integer() | :w
  @type grade :: point() | {:iv, point(), point()}
  @type gtm ::
          {:gvar, non_neg_integer()}
          | {:gtyp, non_neg_integer()}
          | {:glam, grade(), grade(), gtm()}
          | {:gpi, grade(), grade(), gtm()}
          | {:gapp, gtm(), gtm()}
          | :gze
          | {:gsu, gtm()}
          | {:gmatch, gtm(), gtm(), gtm()}

  @doc """
  The image of `book`, including the trailing newline, and the refusals
  of every other exported run.

  `{:ok, image, ""}` is exactly one exported run, and that body erased.
  `{:ok, image, message}` is the first body that erased, and `message`
  names every other exported run. `Muro.emit_mbi/2` writes that file
  and returns `{:error, message}`.
  `{:error, "mbi:entry"}` is a book with no exported run.
  `{:error, message}` is a book whose exported runs all failed. Nothing
  is written by this function.
  """
  def render(book) when is_list(book) do
    case Enum.filter(book, &entry?/1) do
      [] ->
        {:error, "mbi:entry"}

      entries ->
        case choose(Enum.map(entries, &classify(book, &1))) do
          {:ok, gtm, []} ->
            {:ok, show_pure(gtm) <> "\n", ""}

          {:ok, gtm, reasons} ->
            {:ok, show_pure(gtm) <> "\n", Enum.join(reasons, "\n")}

          {:error, reasons} ->
            {:error, Enum.join(reasons, "\n")}
        end
    end
  end

  @doc """
  Erase one de Bruijn term. `{:error, reason}` is the bare tag, without
  the `mbi:` prefix and without a definition name.
  """
  def erase({:var, i}) when is_integer(i) and i >= 0, do: {:ok, {:gvar, i}}

  # The domain is dropped. `glam` opens one binder, the body. A later
  # loader does not recover the domain type.
  def erase({:lam, q, _dom, _name, body}) do
    with {:ok, c, t} <- grades(q),
         {:ok, body} <- erase(body) do
      {:ok, {:glam, c, t, body}}
    end
  end

  # The domain is dropped. `gpi` opens one binder, the same way.
  def erase({:pi, q, _dom, _name, body}) do
    with {:ok, c, t} <- grades(q),
         {:ok, body} <- erase(body) do
      {:ok, {:gpi, c, t, body}}
    end
  end

  def erase({:app, f, a}) do
    with {:ok, f} <- erase(f),
         {:ok, a} <- erase(a) do
      {:ok, {:gapp, f, a}}
    end
  end

  def erase(:ze), do: {:ok, :gze}
  def erase({:su, t}), do: with({:ok, t} <- erase(t), do: {:ok, {:gsu, t}})

  def erase({:nat, n}) when is_integer(n) and n >= 0, do: {:ok, peano(n)}
  def erase({:nat, _}), do: {:error, "numeral"}

  def erase({:mnat, e, _motive, z, s}) do
    with {:ok, e} <- erase(e),
         {:ok, z} <- erase(z),
         {:ok, s} <- erase(s) do
      {:ok, {:gmatch, e, z, s}}
    end
  end

  def erase({:ann, e, _ty}), do: erase(e)

  def erase(:typ), do: {:error, "typ"}
  def erase(:nat), do: {:error, "nat"}
  def erase(:unit), do: {:error, "unit"}
  def erase(:one), do: {:error, "unit"}
  def erase({:munit, _, _, _}), do: {:error, "unit"}
  def erase(:empty), do: {:error, "empty"}
  def erase({:memp, _, _}), do: {:error, "empty"}
  def erase({:mdata, _, _, _}), do: {:error, "data"}
  def erase({:mwbool, _, _, _}), do: {:error, "data"}
  def erase({:mopt, _, _, _}), do: {:error, "data"}
  def erase({:idt, _, _, _}), do: {:error, "id"}
  def erase(:rfl), do: {:error, "id"}
  def erase({:rwt, _, _, _}), do: {:error, "id"}
  def erase({:def, _}), do: {:error, "def"}
  def erase({:prod, _, _}), do: {:error, "pair"}
  def erase({:pair, _, _}), do: {:error, "pair"}
  def erase({:letp, _, _}), do: {:error, "pair"}
  def erase({:nu, _}), do: {:error, "stream"}
  def erase({:unf, _, _}), do: {:error, "stream"}
  def erase({:ucons, _}), do: {:error, "stream"}
  def erase({:bisim, _, _}), do: {:error, "stream"}
  def erase({:stream, _}), do: {:error, "stream"}
  def erase({:always, _, _, _}), do: {:error, "stream"}
  def erase(:i64), do: {:error, "machine"}
  def erase(:f32ty), do: {:error, "machine"}
  def erase({:tensor, _, _}), do: {:error, "machine"}
  def erase({:addi, _, _}), do: {:error, "machine"}
  def erase({:muli, _, _}), do: {:error, "machine"}
  def erase({:addt, _, _}), do: {:error, "machine"}
  def erase({:toi64, _}), do: {:error, "machine"}
  def erase({:packi, _, _}), do: {:error, "machine"}
  def erase({:word, _, _}), do: {:error, "word"}
  def erase(:string), do: {:error, "string"}
  def erase({:slit, _}), do: {:error, "string"}
  def erase({:scat, _, _}), do: {:error, "string"}
  def erase({:slen, _}), do: {:error, "string"}
  def erase({:seq, _, _}), do: {:error, "string"}
  def erase(:bytes), do: {:error, "bytes"}
  def erase(:slice), do: {:error, "bytes"}
  def erase({:blit, _}), do: {:error, "bytes"}
  def erase({:bcat, _, _}), do: {:error, "bytes"}
  def erase({:blen, _}), do: {:error, "bytes"}
  def erase({:beq, _, _}), do: {:error, "bytes"}
  def erase({:xlen, _}), do: {:error, "bytes"}
  def erase({:xeq, _, _}), do: {:error, "bytes"}
  def erase({:bsub, _, _, _}), do: {:error, "bytes"}
  def erase({:bget, _, _}), do: {:error, "bytes"}
  def erase({:aget, _, _}), do: {:error, "bytes"}
  def erase({:bunc, _}), do: {:error, "bytes"}
  def erase({:bfold, _, _, _, _}), do: {:error, "bytes"}
  def erase({:afold, _, _, _, _}), do: {:error, "bytes"}
  def erase({:sbytes, _}), do: {:error, "bytes"}
  def erase({:btil, _, _}), do: {:error, "bytes"}
  def erase({:baft, _, _}), do: {:error, "bytes"}
  def erase(:atom), do: {:error, "atom"}
  def erase({:atom, _}), do: {:error, "atom"}
  def erase({:matom, _, _, _}), do: {:error, "atom"}
  def erase({:hole, _}), do: {:error, "hole"}
  def erase(_), do: {:error, "term"}

  @doc "One line, no trailing newline. The file writer adds the newline."
  def show_pure(gtm) do
    "(muro-beam-image #{@format_version} (boundary #{@boundary_version}) (entry (seq " <>
      show_gtm(gtm) <> " (done))))"
  end

  @doc "The term, without the image wrapper."
  def show_gtm({:gvar, n}), do: "(gvar " <> nat(n) <> ")"
  def show_gtm({:gtyp, n}), do: "(gtyp " <> nat(n) <> ")"
  def show_gtm({:glam, c, t, b}), do: "(glam " <> pair(c, t) <> " " <> show_gtm(b) <> ")"
  def show_gtm({:gpi, c, t, b}), do: "(gpi " <> pair(c, t) <> " " <> show_gtm(b) <> ")"
  def show_gtm({:gapp, f, a}), do: "(gapp " <> show_gtm(f) <> " " <> show_gtm(a) <> ")"
  def show_gtm(:gze), do: "gze"
  def show_gtm({:gsu, e}), do: "(gsu " <> show_gtm(e) <> ")"

  def show_gtm({:gmatch, e, z, s}) do
    "(gmatch " <> show_gtm(e) <> " " <> show_gtm(z) <> " " <> show_gtm(s) <> ")"
  end

  @doc "A grade the way the image spells it. `ω` is `w`."
  def show_grade(n) when is_integer(n) and n >= 0, do: Integer.to_string(n)
  def show_grade(:w), do: "w"

  def show_grade({:iv, a, b}) do
    "(iv " <> show_grade(a) <> " " <> show_grade(b) <> ")"
  end

  defp entry?(%{mode: :run, type: _, body: _, export: false}), do: false
  defp entry?(%{mode: :run, type: _, body: _}), do: true
  defp entry?(_), do: false

  defp classify(book, %{name: name, body: body}) do
    case Ast.to_db(body) do
      {:ok, db} ->
        case erase(db) do
          {:ok, gtm} ->
            {:ok, name, gtm}

          # `{:def, name}` is a definition, a data type, or a constructor.
          # Agda splits those three. A data type and a constructor are `data`.
          {:error, "def"} ->
            {:error, name, def_tag(book, db)}

          {:error, reason} ->
            {:error, name, reason}
        end

      {:error, _} ->
        {:error, name, "term"}
    end
  end

  defp def_tag(book, term) do
    case first_def(term) do
      {:ok, name} -> if data_ref?(book, name), do: "data", else: "def"
      :none -> "def"
    end
  end

  # The first `{:def, _}` `erase` would refuse. The walk follows only the
  # constructors `erase` enters, in the same order.
  defp first_def({:def, name}), do: {:ok, name}

  defp first_def({:lam, q, _, _, body}) do
    case grades(q) do
      {:ok, _, _} -> first_def(body)
      _ -> :none
    end
  end

  defp first_def({:pi, q, _, _, body}) do
    case grades(q) do
      {:ok, _, _} -> first_def(body)
      _ -> :none
    end
  end

  defp first_def({:app, f, a}) do
    case first_def(f) do
      {:ok, _} = hit -> hit
      :none -> first_def(a)
    end
  end

  defp first_def({:su, t}), do: first_def(t)

  defp first_def({:mnat, e, _, z, s}) do
    Enum.reduce_while([e, z, s], :none, fn t, :none ->
      case first_def(t) do
        {:ok, _} = hit -> {:halt, hit}
        :none -> {:cont, :none}
      end
    end)
  end

  defp first_def({:ann, e, _}), do: first_def(e)
  defp first_def(_), do: :none

  defp data_ref?(book, name) when is_binary(name) do
    Enum.any?(book, fn
      %{kind: :data, name: ^name} ->
        true

      %{kind: :data, ctors: ctors} when is_list(ctors) ->
        Enum.any?(ctors, &match?(%{name: ^name}, &1))

      _ ->
        false
    end)
  end

  defp data_ref?(_book, _name), do: false

  defp choose(rows), do: choose(rows, [])

  defp choose([{:error, name, tag} | rest], failed) do
    choose(rest, failed ++ [named(name, tag)])
  end

  defp choose([{:ok, _name, gtm} | rest], failed) do
    {:ok, gtm, failed ++ Enum.map(rest, &rest_reason/1)}
  end

  defp choose([], failed), do: {:error, failed}

  defp rest_reason({:ok, name, _gtm}), do: "mbi:entry in #{name}"
  defp rest_reason({:error, name, tag}), do: named(name, tag)

  defp named(name, tag), do: "mbi:#{tag} in #{name}"

  # A quantity atom. The type grade is 0. A written pair is kept.
  # An unknown quantity is refused.
  defp grades(:affine), do: {:ok, {:iv, 0, 1}, 0}
  defp grades(:reuse), do: {:ok, :w, 0}
  defp grades(:erased), do: {:ok, 0, 0}
  defp grades(:linear), do: {:ok, 1, 0}

  defp grades({:grade, c, t}) do
    with {:ok, c} <- grade(c),
         {:ok, t} <- grade(t) do
      {:ok, c, t}
    end
  end

  defp grades(_), do: {:error, "grade"}

  defp grade(n) when is_integer(n) and n >= 0, do: {:ok, n}
  defp grade(:w), do: {:ok, :w}

  defp grade({:iv, a, b}) do
    with {:ok, a} <- point(a),
         {:ok, b} <- point(b) do
      {:ok, {:iv, a, b}}
    end
  end

  defp grade(_), do: {:error, "grade"}

  defp point(n) when is_integer(n) and n >= 0, do: {:ok, n}
  defp point(:w), do: {:ok, :w}
  defp point(_), do: {:error, "grade"}

  defp peano(n) when is_integer(n) and n >= 0, do: peano(n, :gze)
  defp peano(0, acc), do: acc
  defp peano(n, acc), do: peano(n - 1, {:gsu, acc})

  defp pair(c, t), do: "(" <> show_grade(c) <> " " <> show_grade(t) <> ")"
  defp nat(n) when is_integer(n) and n >= 0, do: Integer.to_string(n)
end
