defmodule MuroVisor.TestEndpoint do
  @moduledoc false

  import ExUnit.Assertions

  @doc """
  Leave the shared endpoint running and not listening.

  A failed bind terminates the child. Later LiveView tests call this
  process, so it has to be running again, with `server: false`.
  """
  def quiet! do
    config =
      case Application.fetch_env(:muro_visor, MuroVisor.Endpoint) do
        {:ok, config} -> config
        :error -> MuroVisor.merge_endpoint([])
      end

    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(config, :server, false))
    ensure!()
  end

  @doc """
  Start the shared endpoint from the current application env.

  Restarts the child when the supervisor is up. Starts the application
  when the supervisor itself is gone.
  """
  def ensure! do
    case Process.whereis(MuroVisor.Supervisor) do
      sup when is_pid(sup) ->
        _ = Supervisor.terminate_child(sup, MuroVisor.Endpoint)
        start_existing!(sup)

      _ ->
        revive!()
    end
  end

  defp start_existing!(sup) do
    case Supervisor.restart_child(sup, MuroVisor.Endpoint) do
      {:ok, _} ->
        :ok

      {:error, :running} ->
        :ok

      {:error, {:already_started, _pid}} ->
        :ok

      {:error, _} ->
        revive!()
    end
  end

  defp revive! do
    _ = Application.stop(:muro_visor)
    {:ok, _} = Application.ensure_all_started(:muro_visor)
    :ok
  end

  @doc """
  The port must not complete a TCP handshake.

  A listener that has just closed answers with `:econnrefused`. OTP 28
  answers the same close with `:econnreset`. A handshake that succeeds
  is tried again for a short time, then this fails.
  """
  def refute_accept!(port) when is_integer(port) and port > 0 do
    case connect_closed(port, 20) do
      {:error, reason} when reason in [:econnrefused, :econnreset] ->
        :ok

      other ->
        flunk("port #{port} was still reachable after shutdown: #{inspect(other)}")
    end
  end

  defp connect_closed(_port, 0), do: :still_open

  defp connect_closed(port, attempts) do
    case :gen_tcp.connect({127, 0, 0, 1}, port, [], 200) do
      {:ok, sock} ->
        _ = :gen_tcp.close(sock)
        Process.sleep(25)
        connect_closed(port, attempts - 1)

      other ->
        other
    end
  end
end
