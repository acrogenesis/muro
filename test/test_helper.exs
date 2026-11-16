# The 4-queens certificate is tagged :slow. `mix test --only slow` includes
# it: an included tag is not excluded.
ExUnit.start(exclude: [:slow])
