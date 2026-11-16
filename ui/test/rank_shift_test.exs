defmodule MuroVisor.RankShiftTest do
  use ExUnit.Case, async: true

  # `@min_track` in `MuroVisor.Draw`. The reference is the scan
  # `disjoint_shift` replaced: the first `k` in `0..limit` that leaves
  # every port at least this far from the previous rank. A rank that
  # never clears returns `limit`, which is what `Enum.find` returned.
  @min_track 6

  test "the first open gap equals the old 0..limit scan" do
    prev0 = MapSet.new([0])
    prev_gap = MapSet.new([0, 12])
    prev_merge = MapSet.new([0, 11])
    prev_far = MapSet.new([100])
    prev_neg = MapSet.new([-4, 3])

    table = [
      {[], MapSet.new()},
      {[], prev0},
      {[0], MapSet.new()},
      {[0], prev0},
      {[0], prev_far},
      {[0], prev_gap},
      {[0], prev_merge},
      {[0, 10], prev0},
      {[0, 1], prev0},
      {[5], prev_neg},
      {[-8, 0, 7], prev_neg},
      {[0, 0, 6], MapSet.new([0, 6, 12])},
      {[2, 2], MapSet.new([2])},
      {[40], MapSet.new(0..8)},
      {Enum.to_list(-3..3), MapSet.new([0, 1, 2, 8])}
    ]

    for {ys, prev} <- table do
      assert MuroVisor.Draw.disjoint_shift(ys, prev) == scan(ys, prev)
    end
  end

  test "random port rows agree with the old scan" do
    for n <- 1..200 do
      :rand.seed(:exsss, {n, 17, 3})
      ys = Enum.map(1..:rand.uniform(8), fn _ -> :rand.uniform(61) - 31 end)
      prev = MapSet.new(Enum.map(1..:rand.uniform(8), fn _ -> :rand.uniform(61) - 31 end))
      assert MuroVisor.Draw.disjoint_shift(ys, prev) == scan(ys, prev)
    end
  end

  defp scan(_ys, prev) when prev == %MapSet{}, do: 0
  defp scan([], _prev), do: 0

  defp scan(ys, prev) do
    limit =
      max(Enum.max(prev) - Enum.min(ys) + @min_track * max(MapSet.size(prev), 1), @min_track)

    Enum.find(0..limit, limit, fn k ->
      Enum.all?(ys, &clear?(&1 + k, prev))
    end)
  end

  defp clear?(y, prev) do
    not Enum.any?(prev, fn p -> abs(p - y) < @min_track end)
  end
end
