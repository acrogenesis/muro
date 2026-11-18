defmodule Muro.FamilyLasso do
  @moduledoc false

  # fail stop refuses no-starve. The prefix is the path to the stutter.
  # The state after `then forever` is that cycle, and `a signal` is held there.
  def text do
    "(held a signal) leads_to (opened a signal) fails in slots after " <>
      "a init 0 opens, a signal 1 held, a init 0 task died, a init 0 server fail stop, " <>
      "a signal 2 held, b init 0 opens, b init 0 task put ok, b init 0 server get (r : Report), " <>
      "b init 0 resolves; then forever: the family has finished: " <>
      "a init 0: running; a signal 1: held; a signal 2: held; b init 0: resolved"
  end
end
