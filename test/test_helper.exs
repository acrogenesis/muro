# The 4-queens certificate is tagged :slow. `mix test --only slow` includes
# it: an included tag is not excluded.
# The keyed-slots script is about 171649 states. Family-graph tests
# share one explore of a given meeting and script.
Application.put_env(:muro, :family_graph_cache, true)

ExUnit.start(exclude: [:slow])
