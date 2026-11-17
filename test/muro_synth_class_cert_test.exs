defmodule Muro.SynthClassCertTest do
  use ExUnit.Case, async: true

  alias Muro.Synth.ClassCert

  @actions ~w(c0 c1 c2 c3)

  test "a lone arm that prefers a miss is refused" do
    pred =
      {:or, {:feat, "has-pos-reward-c0"}, {:not, {:other, "reaches-pos", "c3", []}}}

    arm = %{pred: pred, action: "c3", else: "c0"}

    assert {:skip, reason} = ClassCert.scan(@actions, [arm])
    assert reason =~ "does not reach"
  end

  test "the queens4 reach cascade has no bad row" do
    assert :ok = ClassCert.scan(@actions, queens4_arms())
  end

  test "a wrong arm is a typed refusal and not a cover split" do
    actions = @actions
    {:ok, host} = Muro.Synth.Host.open("examples/cshrl/envs/queens4.muro")
    {:ok, specs} = Muro.Synth.Feature.extend_reach(host)
    host = Muro.Synth.Host.install_features(host, specs)

    pred =
      {:or, {:feat, "has-pos-reward-c0"},
       {:not, {:other, "reaches-pos", "c3", for(a <- actions, a != "c3", do: "reaches-pos-#{a}")}}}

    arm = %{
      name: "survivor-c3",
      pred: pred,
      action: "c3",
      else: "c0",
      observations: [],
      kept: []
    }

    refute ClassCert.recur_only?(host, [arm], "coind-homo")

    assert {:ok, source, meta} =
             Muro.Synth.Book.render(host, [arm], "examples/cshrl/envs", "coind-homo")

    assert meta.kind == :policy
    assert meta.reason =~ "does not reach"
    refute source =~ "evidence CoindHomo"
    refute source =~ "cert-cover-miss"
    refute source =~ "find-policy"
    refute source =~ "find-ranking"
  end

  test "reach-family detection stays on the reach stems" do
    refute ClassCert.family?(true, @actions)
    refute ClassCert.family?(false, @actions)
    refute ClassCert.family?({:feat, "is-self-loop-c0"}, @actions)
    refute ClassCert.family?({:feat, "leads-terminal-c1"}, @actions)

    assert ClassCert.family?({:feat, "reaches-pos-c1"}, @actions)
    assert ClassCert.family?({:feat, "has-pos-reward-c0"}, @actions)
    assert ClassCert.family?(hd(queens4_arms()).pred, @actions)
  end

  defp queens4_arms do
    others = fn action ->
      for other <- @actions, other != action, do: "reaches-pos-#{other}"
    end

    spec = fn action, pred ->
      %{name: "survivor-#{action}", pred: pred, action: action, else: "c0", observations: []}
    end

    [
      spec.(
        "c0",
        {:or, {:feat, "has-pos-reward-c0"}, {:not, {:other, "reaches-pos", "c0", others.("c0")}}}
      ),
      spec.(
        "c1",
        {:or, {:feat, "reaches-pos-c1"}, {:not, {:other, "reaches-pos", "c1", others.("c1")}}}
      ),
      spec.(
        "c2",
        {:or, {:feat, "reaches-pos-c2"}, {:not, {:other, "reaches-pos", "c2", others.("c2")}}}
      ),
      spec.(
        "c3",
        {:or, {:feat, "has-pos-reward-c0"}, {:not, {:other, "reaches-pos", "c3", others.("c3")}}}
      )
    ]
  end
end
