defmodule MuroVisor.LayoutTest do
  use MuroVisor.ConnCase, async: false

  @moduletag timeout: 180_000

  test "every book that checks has a stable layered layout" do
    root = Path.expand("../../examples", __DIR__)

    loaded =
      root
      |> Path.join("**/*.muro")
      |> Path.wildcard()
      |> Enum.sort()
      |> Enum.flat_map(fn path ->
        case Muro.Load.file(path) do
          {:ok, book} -> [{Path.relative_to(path, root), book}]
          {:error, _} -> []
        end
      end)

    assert loaded != []

    for {name, book} <- loaded do
      assert_layout(Muro.Explore.graph(book), name)
    end
  end

  test "small graphs keep nodes apart and edges on their own paths" do
    assert_layout(chain(4), "chain")
    assert_layout(cycle(), "cycle")
    assert_layout(self_loop(), "self")
    assert_layout(parallel(), "parallel")
    assert_layout(empty_graph(), "empty")
    assert_layout(single(), "single")
    assert_layout(compound(), "compound")

    wide = MuroVisor.Draw.layout(row(8))
    assert length(Enum.uniq(Enum.map(wide.nodes, & &1.x))) >= 2
    assert wide.width > wide.height

    chain = MuroVisor.Draw.layout(chain(4))
    assert chain.width > chain.height
    assert length(Enum.uniq(Enum.map(chain.nodes, & &1.x))) == 4

    loop = MuroVisor.Draw.layout(self_loop())
    edge = hd(loop.edges)
    assert edge.d =~ " C "
    [{x1, y1}, {x2, y2}] = endpoints(edge.d)
    assert {x1, y1} != {x2, y2}
    assert on_boundary?(x1, y1, hd(loop.nodes))
    assert on_boundary?(x2, y2, hd(loop.nodes))

    paths = MuroVisor.Draw.layout(parallel()).edges |> Enum.map(& &1.d)
    assert length(Enum.uniq(paths)) == 2

    box = MuroVisor.Draw.layout(compound())
    [node] = box.nodes
    [meet] = node.meetings
    assert Enum.any?(meet.transitions, &(&1.d =~ " C "))
    assert Enum.any?(meet.transitions, &(&1.d =~ " L "))
  end

  test "nodes, edges, and configurations are keyboard controls", %{conn: conn} do
    view = open_book(conn, example("meet.muro"))
    html = render(view)
    graph = Muro.Explore.graph(book())
    picture = MuroVisor.Draw.layout(graph)

    assert picture.width > 600
    assert length(Enum.uniq(Enum.map(picture.nodes, & &1.x))) > 1

    node = Enum.find(definition_nodes(html), &(&1.name =~ "pong"))
    assert node
    selected = view |> element("##{node.id}") |> render_keydown(%{"key" => "Enter"})
    assert text_of(selected, "#detail-title") == "pong"

    kept = text_of(selected, "#detail-title")

    ignored = view |> element("##{node.id}") |> render_keydown(%{"key" => "Escape"})
    assert text_of(ignored, "#detail-title") == kept

    clicked = view |> element("##{node.id}") |> render_click()
    assert text_of(clicked, "#detail-title") == "pong"
    assert attr_class(clicked, "##{node.id}") =~ "selected"

    edge = hd(use_edges(html))
    assert edge_path(html, edge.id) != nil
    keyed = view |> element("##{edge.id}") |> render_keydown(%{"key" => " "})
    assert text_of(keyed, "#detail-title") != ""
    assert attr_class(keyed, "##{edge.id} path.edge") =~ "selected"

    page = html_response(get(conn, "/"), 200)
    assert page =~ "overflow-wrap: anywhere"
    refute page =~ "overflow-wrap: normal"
    assert page =~ "overflow-x: hidden"
    assert page =~ "#outline pre"

    child = hd(Enum.find(graph.nodes, &(&1.children != [])).children)
    view |> element("#configuration-#{child.id}") |> render_keydown(%{"key" => "Enter"})
    assert text_of(render(view), "#detail-loc") =~ "meet.muro"

    for edge <- use_edges(render(view)) do
      assert edge_path(render(view), edge.id) =~ ~r/[MLC]/
    end

    assert html =~ "tabindex=\"0\""
    assert html =~ "role=\"button\""
    assert html =~ "id=\"outline-names\""
    assert html =~ "id=\"outline-layouts\""
    assert html =~ "id=\"zoom-fit\""
    assert html =~ "id=\"zoom-150\""
  end

  test "the definitions view keeps labels readable and focus is not a box", %{conn: conn} do
    page = html_response(get(conn, "/?view=all"), 200)

    assert page =~ ~s(id="zoom-fit")
    assert page =~ "checked"
    assert page =~ "#zoom-fit:checked ~ .graph-scroll svg#book-graph"
    assert page =~ "calc(var(--native-width) * 11 / 12)"
    assert page =~ "100cqw - 24px"
    assert page =~ "100cqh - 24px"
    assert page =~ "aspect-ratio: var(--native-width) / var(--native-height)"
    assert page =~ "#zoom-100:checked ~ .graph-scroll svg#book-graph"
    assert page =~ "#zoom-150:checked ~ .graph-scroll svg#book-graph"
    assert page =~ "aspect-ratio: auto"
    assert page =~ ~s(preserveAspectRatio="xMidYMid meet")
    assert page =~ "--native-height:"
    assert page =~ "font: 12px"

    assert page =~
             "svg text { font: 12px ui-sans-serif, sans-serif; fill: #1c1917; stroke: none; }"

    assert page =~ "paint-order: stroke fill"
    refute page =~ "0.75"

    assert page =~ "svg rect.cluster-frame { fill: #fafaf9; stroke: #d6d3d1; stroke-width: 1px; }"

    assert page =~
             "svg .edge-dual { stroke: #1e3a8a; stroke-width: 1.5px; stroke-dasharray: 8 5; }"

    assert page =~ "svg g:focus, svg g:focus-visible { outline: none; }"
    assert page =~ "svg g:focus-visible > path.edge"
    assert page =~ "path.edge.selected + text"
    refute page =~ "svg g:focus { outline: 2px"
  end

  defp assert_layout(graph, label) do
    once = MuroVisor.Draw.layout(graph)
    assert once == MuroVisor.Draw.layout(graph), "#{label} is not stable"
    assert once.width >= 32
    assert once.height >= 32
    assert_no_overlap(once.nodes, label)

    by_id = Map.new(once.nodes, &{&1.id, &1})

    for edge <- once.edges do
      assert_endpoints(edge.d, Map.fetch!(by_id, edge.from), Map.fetch!(by_id, edge.to), label)
      assert_label(edge, once, label)
    end

    assert_within_layers(once, label)

    for node <- once.nodes, meet <- node.meetings do
      assert_within_layers(%{nodes: meet.children, edges: meet.transitions}, label)
    end

    for node <- once.nodes, meet <- node.meetings do
      assert contained?(meet, node), "#{label} meeting spills out of #{node.name}"
      assert_no_overlap(meet.children, label)

      for child <- meet.children do
        assert contained?(child, meet), "#{label} configuration spills out of #{meet.name}"
      end
    end

    trans_edges =
      for node <- once.nodes, meet <- node.meetings, trans <- meet.transitions do
        kids = Map.new(meet.children, &{&1.id, &1})
        assert_endpoints(trans.d, Map.fetch!(kids, trans.from), Map.fetch!(kids, trans.to), label)
        assert_label(trans, once, label)
        trans
      end

    paths = Enum.map(once.edges, & &1.d) ++ Enum.map(trans_edges, & &1.d)
    assert_distinct_paths(paths, label)
    assert_no_collinear_overlap(once.edges ++ trans_edges, label)
    assert_track_spacing(once.edges ++ trans_edges, layout_boxes(once), label)
    assert_distinct_ports(once.nodes, once.edges, label)
    assert_badges_clear(once, label)

    for node <- once.nodes, meet <- node.meetings do
      assert_distinct_ports(meet.children, meet.transitions, label)
    end
  end

  defp assert_badges_clear(picture, label) do
    badges =
      for edge <- picture.edges, Map.has_key?(edge, :bw) do
        %{x: edge.bx, y: edge.by, w: edge.bw, h: edge.bh, id: edge.id}
      end

    nodes = Enum.map(picture.nodes, &%{x: &1.x, y: &1.y, w: &1.w, h: &1.h, id: &1.id})

    for {a, i} <- Enum.with_index(badges), {b, j} <- Enum.with_index(badges), i < j do
      refute overlap?(inflate(a, 1), b), "#{label} badges #{a.id} and #{b.id} overlap"
    end

    for badge <- badges, node <- nodes do
      refute overlap?(inflate(badge, 1), node),
             "#{label} badge #{badge.id} overlaps #{node.id}"
    end
  end

  defp inflate(box, n),
    do: %{box | x: box.x - n, y: box.y - n, w: box.w + 2 * n, h: box.h + 2 * n}

  defp assert_no_overlap(boxes, label) do
    for {a, i} <- Enum.with_index(boxes), {b, j} <- Enum.with_index(boxes), i < j do
      refute overlap?(a, b), "#{label} overlaps #{a.id} and #{b.id}"
    end
  end

  defp overlap?(a, b) do
    a.x < b.x + b.w and b.x < a.x + a.w and a.y < b.y + b.h and b.y < a.y + a.h
  end

  defp contained?(inner, outer) do
    inner.x >= outer.x and inner.y >= outer.y and
      inner.x + inner.w <= outer.x + outer.w and
      inner.y + inner.h <= outer.y + outer.h
  end

  defp assert_endpoints(d, from, to, label) do
    [{x1, y1}, {x2, y2}] = endpoints(d)
    assert on_boundary?(x1, y1, from), "#{label} leaves #{from.id} at #{x1},#{y1}"
    assert on_boundary?(x2, y2, to), "#{label} arrives #{to.id} at #{x2},#{y2}"
  end

  defp endpoints(d) do
    pairs = numbers(d)
    [List.first(pairs), List.last(pairs)]
  end

  defp on_boundary?(x, y, rect) do
    in_x = x >= rect.x and x <= rect.x + rect.w
    in_y = y >= rect.y and y <= rect.y + rect.h
    on_x = x == rect.x or x == rect.x + rect.w
    on_y = y == rect.y or y == rect.y + rect.h
    (on_x and in_y) or (on_y and in_x)
  end

  defp assert_label(%{label: label, lx: lx, ly: ly}, picture, name) do
    box = %{x: lx, y: ly - 12, w: max(String.length(label), 1) * 7, h: 14}
    assert box.x >= 0, name
    assert box.y >= 0, name
    assert box.x + box.w <= picture.width, "#{name} clips #{label}"
    assert box.y + box.h <= picture.height, "#{name} clips #{label}"
  end

  defp assert_within_layers(%{nodes: nodes, edges: edges}, label) when nodes != [] do
    layers = layers_of(nodes)

    index =
      Map.new(nodes, fn node ->
        {node.id, layer_index(layers, node)}
      end)

    for edge <- edges,
        edge.from != edge.to,
        Map.has_key?(index, edge.from),
        Map.has_key?(index, edge.to) do
      lo = min(index[edge.from], index[edge.to])
      hi = max(index[edge.from], index[edge.to])
      box = layers |> Enum.slice(lo..hi) |> union_boxes() |> expand_box(160)

      for {{x1, y1}, {x2, y2}} <- segments(edge.d) do
        assert in_box?(x1, y1, box),
               "#{label} #{edge.id} leaves its layers at #{x1},#{y1}"

        assert in_box?(x2, y2, box),
               "#{label} #{edge.id} leaves its layers at #{x2},#{y2}"
      end
    end
  end

  defp assert_within_layers(_picture, _label), do: :ok

  defp layers_of(nodes) do
    nodes
    |> Enum.group_by(& &1.x)
    |> Enum.sort_by(fn {x, _} -> x end)
    |> Enum.map(fn {_x, group} -> box_of(group) end)
  end

  defp layer_index(layers, node) do
    case Enum.find_index(layers, fn box ->
           node.x >= box.x and node.x + node.w <= box.x + box.w and node.y >= box.y and
             node.y + node.h <= box.y + box.h
         end) do
      nil -> flunk("no layer contains #{node.id}")
      index -> index
    end
  end

  defp box_of(nodes) do
    x = Enum.min(Enum.map(nodes, & &1.x))
    y = Enum.min(Enum.map(nodes, & &1.y))
    right = Enum.max(Enum.map(nodes, &(&1.x + &1.w)))
    bottom = Enum.max(Enum.map(nodes, &(&1.y + &1.h)))
    %{x: x, y: y, w: right - x, h: bottom - y}
  end

  defp union_boxes([box]), do: box

  defp union_boxes(boxes) do
    x = Enum.min(Enum.map(boxes, & &1.x))
    y = Enum.min(Enum.map(boxes, & &1.y))
    right = Enum.max(Enum.map(boxes, &(&1.x + &1.w)))
    bottom = Enum.max(Enum.map(boxes, &(&1.y + &1.h)))
    %{x: x, y: y, w: right - x, h: bottom - y}
  end

  defp expand_box(box, margin) do
    %{x: box.x - margin, y: box.y - margin, w: box.w + 2 * margin, h: box.h + 2 * margin}
  end

  defp in_box?(x, y, box) do
    x >= box.x and y >= box.y and x <= box.x + box.w and y <= box.y + box.h
  end

  defp attr_class(html, selector) do
    html
    |> parse()
    |> Floki.attribute(selector, "class")
    |> List.first()
    |> to_string()
  end

  defp assert_distinct_paths(paths, label) do
    assert length(paths) == length(Enum.uniq(paths)), "#{label} reuses a path"

    tagged =
      paths
      |> Enum.with_index()
      |> Enum.flat_map(fn {d, i} ->
        for seg <- segments(d), do: {i, seg}
      end)

    for {_line, spans} <- axis_spans(tagged, fn {i, _} -> i end) do
      refute_shared_span(spans, label, fn _a, _b -> "#{label} edges share a line" end)
    end
  end

  defp assert_no_collinear_overlap(edges, label) do
    tagged = for edge <- edges, seg <- segments(edge.d), do: {edge, seg}

    for {_line, spans} <- axis_spans(tagged, fn {edge, _} -> edge end) do
      refute_shared_span(spans, label, fn e1, e2 ->
        if shares_node?(e1, e2), do: nil, else: "#{label} #{e1.id} overlaps #{e2.id}"
      end)
    end
  end

  defp layout_boxes(picture) do
    Enum.flat_map(picture.nodes, fn node ->
      kids = Enum.flat_map(node.meetings, & &1.children)
      [node | kids]
    end)
  end

  # Channel tracks and stubs that leave different nodes stay a few pixels apart.
  # Stubs that share one node are the ports on that side.
  defp assert_track_spacing(edges, nodes, label) do
    indexed = for edge <- edges, seg <- segments(edge.d), do: {edge.id, seg}

    indexed
    |> axis_groups()
    |> Enum.each(fn groups -> refute_close_tracks(groups, nodes, label) end)
  end

  # Segments that can share a line, grouped by that line. The owner is
  # whatever `owner` reads off the tagged pair. A sweep on one line
  # replaces the pairs of every edge.
  defp axis_spans(tagged, owner) do
    {horiz, vert} = split_axes(tagged)

    Enum.concat(
      group_line(horiz, owner, fn {{x1, _y1}, {x2, _y2}} -> {min(x1, x2), max(x1, x2)} end),
      group_line(vert, owner, fn {{_x1, y1}, {_x2, y2}} -> {min(y1, y2), max(y1, y2)} end)
    )
  end

  defp axis_groups(tagged) do
    {horiz, vert} = split_axes(tagged)

    [
      group_tracks(horiz, fn {{x1, y}, {x2, _}} -> {y, min(x1, x2), max(x1, x2)} end),
      group_tracks(vert, fn {{x, y1}, {_, y2}} -> {x, min(y1, y2), max(y1, y2)} end)
    ]
  end

  defp split_axes(tagged) do
    Enum.reduce(tagged, {[], []}, fn {_owner, {{x1, y1}, {x2, y2}}} = item, {h, v} ->
      cond do
        y1 == y2 and x1 != x2 -> {[item | h], v}
        x1 == x2 and y1 != y2 -> {h, [item | v]}
        true -> {h, v}
      end
    end)
  end

  defp group_line(items, owner, span) do
    items
    |> Enum.group_by(
      fn {_tag, {{x1, y1}, {_x2, y2}}} -> if y1 == y2, do: y1, else: x1 end,
      fn item ->
        {lo, hi} = span.(elem(item, 1))
        {owner.(item), lo, hi}
      end
    )
  end

  defp group_tracks(items, pack) do
    Enum.group_by(items, fn {_id, seg} -> elem(pack.(seg), 0) end, fn {id, seg} ->
      {_line, lo, hi} = pack.(seg)
      {id, lo, hi, seg}
    end)
  end

  defp refute_shared_span(spans, _label, message) do
    spans
    |> Enum.sort_by(fn {_owner, lo, _hi} -> lo end)
    |> Enum.reduce([], fn {owner, lo, hi}, active ->
      active = Enum.reject(active, fn {_owner, end_} -> end_ <= lo end)

      Enum.each(active, fn {other, _end} ->
        if owner != other do
          case message.(owner, other) do
            nil -> :ok
            text -> flunk(text)
          end
        end
      end)

      [{owner, hi} | active]
    end)
  end

  defp refute_close_tracks(groups, nodes, label) do
    groups
    |> Enum.sort_by(fn {line, _spans} -> line end)
    |> Enum.reduce([], fn {line, spans}, earlier ->
      window = Enum.filter(earlier, fn {prev, _} -> line - prev < 6 end)

      for {prev, old} <- window,
          gap = line - prev,
          gap > 0,
          {id1, lo1, hi1, s1} <- spans,
          {id2, lo2, hi2, s2} <- old,
          id1 != id2,
          ranges_overlap?(lo1, hi1, lo2, hi2),
          not same_node_stubs?(s1, s2, nodes) do
        flunk("#{label} #{id1} and #{id2} run #{gap}px apart")
      end

      [{line, spans} | window]
    end)
  end

  defp same_node_stubs?(s1, s2, nodes) do
    case {stub_node(s1, nodes), stub_node(s2, nodes)} do
      {id, id} when not is_nil(id) -> true
      _ -> false
    end
  end

  defp stub_node({{x1, y1}, {x2, y2}}, nodes) do
    case Enum.filter(nodes, &(on_boundary?(x1, y1, &1) or on_boundary?(x2, y2, &1))) do
      [node] -> node.id
      _ -> nil
    end
  end

  defp shares_node?(a, b) do
    MapSet.size(MapSet.intersection(MapSet.new([a.from, a.to]), MapSet.new([b.from, b.to]))) > 0
  end

  defp assert_distinct_ports(nodes, edges, label) do
    by_id = Map.new(nodes, &{&1.id, &1})

    groups =
      for edge <- edges,
          pts = numbers(edge.d),
          {nid, {x, y}} <- [{edge.from, List.first(pts)}, {edge.to, List.last(pts)}],
          node = Map.get(by_id, nid),
          side = port_side(x, y, node),
          side != nil do
        {{node.id, side}, {x, y}}
      end
      |> Enum.group_by(&elem(&1, 0), &elem(&1, 1))

    for {{id, side}, pts} <- groups do
      assert length(pts) == length(Enum.uniq(pts)),
             "#{label} repeats a port on #{id} #{side}"
    end
  end

  defp port_side(x, y, node) do
    cond do
      x == node.x and y >= node.y and y <= node.y + node.h -> :left
      x == node.x + node.w and y >= node.y and y <= node.y + node.h -> :right
      y == node.y and x >= node.x and x <= node.x + node.w -> :top
      y == node.y + node.h and x >= node.x and x <= node.x + node.w -> :bottom
      true -> nil
    end
  end

  defp segments(d) do
    tokens = Regex.scan(~r/[MLC]|-?\d+/, d) |> Enum.map(&hd/1)
    walk(tokens, nil, [])
  end

  defp walk([], _cur, acc), do: acc
  defp walk(["M", x, y | rest], _cur, acc), do: walk(rest, {int(x), int(y)}, acc)

  defp walk(["L", x, y | rest], {px, py}, acc) do
    nxt = {int(x), int(y)}
    acc = if nxt == {px, py}, do: acc, else: [{{px, py}, nxt} | acc]
    walk(rest, nxt, acc)
  end

  defp walk(["C", _a, _b, _c, _d, x, y | rest], _cur, acc) do
    walk(rest, {int(x), int(y)}, acc)
  end

  defp ranges_overlap?(a1, a2, b1, b2), do: max(a1, b1) < min(a2, b2)

  defp numbers(d) do
    Regex.scan(~r/-?\d+/, d)
    |> Enum.map(fn [n] -> String.to_integer(n) end)
    |> Enum.chunk_every(2)
    |> Enum.map(fn [x, y] -> {x, y} end)
  end

  defp int(n), do: String.to_integer(n)

  defp edge_path(html, id) do
    html
    |> parse()
    |> Floki.find("##{id} path")
    |> Enum.find_value(fn path ->
      case Floki.attribute(path, "d") do
        [d | _] -> d
        [] -> nil
      end
    end)
  end

  defp node(id, name),
    do: %{id: id, name: name, mode: :run, kind: :def, children: [], transitions: []}

  defp edge(id, from, to), do: %{id: id, from: from, to: to, use: :def}

  defp chain(n) do
    nodes = Enum.map(1..n, &node("n#{&1}", "n#{&1}"))

    edges =
      Enum.map(1..(n - 1), fn i -> edge("e#{i}", "n#{i}", "n#{i + 1}") end)

    %{nodes: nodes, edges: edges}
  end

  defp row(n) do
    %{nodes: Enum.map(1..n, &node("n#{&1}", "n#{&1}")), edges: []}
  end

  defp cycle do
    %{
      nodes: [node("a", "a"), node("b", "b"), node("c", "c")],
      edges: [edge("e1", "a", "b"), edge("e2", "b", "c"), edge("e3", "c", "a")]
    }
  end

  defp self_loop do
    %{nodes: [node("a", "loop")], edges: [edge("e0", "a", "a")]}
  end

  defp parallel do
    %{
      nodes: [node("a", "a"), node("b", "b")],
      edges: [edge("e1", "a", "b"), edge("e2", "a", "b")]
    }
  end

  defp empty_graph, do: %{nodes: [], edges: []}

  defp single, do: %{nodes: [node("a", "only")], edges: []}

  defp compound do
    %{
      nodes: [
        %{
          id: "ping",
          name: "ping",
          mode: :run,
          kind: :session,
          children: [
            %{id: "cfg-ping-wire-0", meeting: "wire"},
            %{id: "cfg-ping-wire-1", meeting: "wire"}
          ],
          transitions: [
            %{
              from: "cfg-ping-wire-0",
              to: "cfg-ping-wire-1",
              label: ["put", "1"],
              meeting: "wire"
            },
            %{
              from: "cfg-ping-wire-1",
              to: "cfg-ping-wire-1",
              label: ["put", "k"],
              meeting: "wire"
            }
          ]
        }
      ],
      edges: []
    }
  end
end
