defmodule Muro.WordLink do
  @moduledoc false

  # The same cases as agda/Muro/WordLink.agda `decide`. Names are the
  # strings in the term. Agda looks the same strings up by index.
  # The type is matched as written: plus and Le are not reduced.

  @unsigned "word-to-Nat lemmas are unsigned"
  @wrap "wlink expected a checked unsigned operation"
  @width "wlink width does not match"
  @op "wlink operation does not match"
  @shape "wlink does not prove this type"

  @mod %{u8: 256, u32: 4_294_967_296, u64: 18_446_744_073_709_551_616}
  @nat_ops ["plus", "minus", "times"]

  @doc """
  `:ok` when `hyp` and `goal` are one unsigned word-to-Nat statement.
  Otherwise `{:error, message}`.
  """
  def accept(hyp, goal) do
    case hyp do
      {:idt, a, lhs, rhs} -> from_hyp(a, lhs, rhs, goal)
      _ -> from_bound(hyp, goal)
    end
  end

  # fromHyp
  defp from_hyp(a, lhs, rhs, goal) do
    cond do
      wrap?(lhs) ->
        {:error, @wrap}

      signed_opt?(a) ->
        {:error, @unsigned}

      true ->
        case {chk_side(lhs), opt_width(a), some?(rhs)} do
          {{:ok, side, x, y}, {:ok, w}, {:ok, c}} ->
            best(try_val(side, x, y, c, goal), try_fit(side, w, x, y, goal))

          _ ->
            {:error, @shape}
        end
    end
  end

  # fromBound
  defp from_bound(hyp, goal) do
    case goal do
      {:idt, opt, lhs, rhs} ->
        cond do
          wrap?(lhs) -> {:error, @wrap}
          signed_opt?(opt) -> {:error, @unsigned}
          true -> from_bound_chk(hyp, opt, lhs, rhs)
        end

      _ ->
        {:error, @shape}
    end
  end

  defp from_bound_chk(hyp, opt, lhs, rhs) do
    case chk_side(lhs) do
      :no ->
        {:error, @shape}

      {:ok, side, x, y} ->
        case opt_width(opt) do
          :no ->
            {:error, @shape}

          {:ok, w} ->
            case some?(rhs) do
              :no -> {:error, @shape}
              {:ok, pay} -> from_of(hyp, side, w, x, y, pay)
            end
        end
    end
  end

  # fromOf: toI64 is unsigned, another unsigned width is width.
  defp from_of(hyp, side, w, x, y, pay) do
    case of_view(pay) do
      :no ->
        {:error, @shape}

      :i64 ->
        {:error, @unsigned}

      {:ok, w2, n} ->
        if w2 == w do
          case payload_bin(side, x, y, n) do
            :ok -> bound_hyp(side, w, x, y, hyp)
            :shape -> {:error, @shape}
            {:error, _} = err -> err
          end
        else
          {:error, @width}
        end
    end
  end

  # tryVal. expect_nat stays outside `with`, so an operation error is kept.
  defp try_val(side, a, b, c, goal) do
    case val_shape(a, b, c, goal) do
      {:ok, name} -> expect_nat(name, op_name(side))
      :shape -> {:error, @shape}
    end
  end

  defp val_shape(a, b, c, {:idt, :nat, gl, gr}) do
    if gl == ton(c) do
      case binop(gr) do
        {:ok, name, x, y} ->
          if x == ton(a) and y == ton(b), do: {:ok, name}, else: :shape

        :no ->
          :shape
      end
    else
      :shape
    end
  end

  defp val_shape(_, _, _, _), do: :shape

  # tryFit
  defp try_fit(:sub, _w, a, b, goal), do: try_fit_sub(a, b, goal)

  defp try_fit(side, w, a, b, goal) when side in [:add, :mul] do
    case fit_shape(a, b, goal) do
      {:ok, name, mod} ->
        case expect_nat(name, op_name(side)) do
          :ok -> modulus_msg(w, mod)
          err -> err
        end

      :shape ->
        {:error, @shape}

      {:error, _} = err ->
        err
    end
  end

  defp try_fit_sub(a, b, {:app, {:app, {:def, j}, x}, y}) do
    case expect_nat(j, "Le") do
      :ok -> if x == ton(b) and y == ton(a), do: :ok, else: {:error, @shape}
      err -> err
    end
  end

  defp try_fit_sub(_, _, _), do: {:error, @shape}

  defp fit_shape(a, b, {:app, {:app, {:def, j}, {:su, body}}, mod}) do
    case expect_nat(j, "Le") do
      :ok ->
        case binop(body) do
          {:ok, name, x, y} ->
            if x == ton(a) and y == ton(b), do: {:ok, name, mod}, else: :shape

          :no ->
            :shape
        end

      err ->
        err
    end
  end

  defp fit_shape(_, _, _), do: :shape

  # payloadOf / expectName, then boundHyp.
  defp payload_bin(side, a, b, term) do
    case binop(term) do
      {:ok, name, x, y} ->
        if x == ton(a) and y == ton(b) do
          case expect_nat(name, op_name(side)) do
            :ok -> :ok
            err -> err
          end
        else
          :shape
        end

      :no ->
        :shape
    end
  end

  defp bound_hyp(side, w, a, b, hyp) when side in [:add, :mul] do
    case hyp do
      {:app, {:app, {:def, j}, {:su, body}}, mod} ->
        case expect_nat(j, "Le") do
          :ok ->
            if body == bin(op_name(side), ton(a), ton(b)) do
              modulus_msg(w, mod)
            else
              {:error, op_or_shape(side, body)}
            end

          err ->
            err
        end

      _ ->
        {:error, @shape}
    end
  end

  defp bound_hyp(:sub, _w, a, b, hyp) do
    case hyp do
      {:app, {:app, {:def, j}, x}, y} ->
        case expect_nat(j, "Le") do
          :ok -> if x == ton(b) and y == ton(a), do: :ok, else: {:error, @shape}
          err -> err
        end

      _ ->
        {:error, @shape}
    end
  end

  # expectName
  defp expect_nat(name, want) when name == want, do: :ok
  defp expect_nat(name, _want) when name in @nat_ops, do: {:error, @op}
  defp expect_nat(_name, _want), do: {:error, @shape}

  # opOrShape
  defp op_or_shape(side, term) do
    case binop(term) do
      {:ok, name, _, _} ->
        if name in @nat_ops and name != op_name(side), do: @op, else: @shape

      :no ->
        @shape
    end
  end

  # mod?
  defp modulus_msg(w, mod) do
    case modulus_class(w, mod) do
      :here -> :ok
      :other -> {:error, @width}
      :no -> {:error, @shape}
    end
  end

  defp modulus_class(w, term) do
    case read_nat(term) do
      {:ok, n} ->
        cond do
          n == Map.fetch!(@mod, w) -> :here
          other_width?(n, w) -> :other
          true -> :no
        end

      :error ->
        :no
    end
  end

  defp other_width?(n, w) do
    Enum.any?(@mod, fn {k, m} -> k != w and n == m end)
  end

  defp read_nat({:nat, n}) when is_integer(n) and n >= 0, do: {:ok, n}
  defp read_nat(:ze), do: {:ok, 0}

  defp read_nat({:su, t}) do
    case read_nat(t) do
      {:ok, n} -> {:ok, n + 1}
      :error -> :error
    end
  end

  defp read_nat(_), do: :error

  defp best(:ok, _), do: :ok
  defp best({:error, _}, :ok), do: :ok
  defp best({:error, e1}, {:error, e2}), do: {:error, sharper(e1, e2)}

  defp sharper(e1, e2) do
    if rank(e1) < rank(e2), do: e2, else: e1
  end

  defp rank(@width), do: 2
  defp rank(@op), do: 1
  defp rank(_), do: 0

  defp wrap?({:word, op, _}) when op in [:add, :sub, :mul], do: true
  defp wrap?(_), do: false

  defp signed_opt?({:word, {:optk, :i64}, []}), do: true
  defp signed_opt?({:word, :opt, [:i64]}), do: true
  defp signed_opt?({:word, :opt, [{:word, {:ty, :i64}, []}]}), do: true
  defp signed_opt?(_), do: false

  defp opt_width({:word, {:optk, k}, []}) when k in [:u8, :u32, :u64], do: {:ok, k}

  defp opt_width({:word, :opt, [{:word, {:ty, k}, []}]}) when k in [:u8, :u32, :u64],
    do: {:ok, k}

  defp opt_width(_), do: :no

  defp chk_side({:word, :cadd, [a, b]}), do: {:ok, :add, a, b}
  defp chk_side({:word, :csub, [a, b]}), do: {:ok, :sub, a, b}
  defp chk_side({:word, :cmul, [a, b]}), do: {:ok, :mul, a, b}
  defp chk_side(_), do: :no

  defp some?({:word, :some, [c]}), do: {:ok, c}
  defp some?(_), do: :no

  defp of_view({:word, {:of, :i64}, [_]}), do: :i64
  defp of_view({:word, {:of, k}, [n]}) when k in [:u8, :u32, :u64], do: {:ok, k, n}
  defp of_view(_), do: :no

  defp binop({:app, {:app, {:def, name}, x}, y}) when is_binary(name), do: {:ok, name, x, y}
  defp binop(_), do: :no

  defp op_name(:add), do: "plus"
  defp op_name(:sub), do: "minus"
  defp op_name(:mul), do: "times"

  defp ton(x), do: {:word, :ton, [x]}
  defp bin(name, x, y), do: {:app, {:app, {:def, name}, x}, y}
end
