import pytest

from miasm.core.graph import *

@pytest.fixture
def g():
    g = DiGraph()
    g.add_node('a')
    g.add_node('b')

    g.add_edge('a', 'b')
    g.add_edge('a', 'c')
    g.add_edge('a', 'c')
    g.add_edge('c', 'c')

    return g


def test_print(g):
    print(g)

    print([x for x in g.successors('a')])
    print([x for x in g.predecessors('a')])
    print([x for x in g.predecessors('b')])
    print([x for x in g.predecessors('c')])
    print([x for x in g.successors('c')])


@pytest.fixture
def g1():
    g1 = DiGraph()
    g1.add_edge(1, 2)
    g1.add_edge(2, 3)
    g1.add_edge(2, 4)
    g1.add_edge(3, 5)
    g1.add_edge(4, 5)
    g1.add_edge(5, 2)
    g1.add_edge(2, 6)
    return g1


def test_dominators(g1):
    """
    Test from: https://en.wikipedia.org/wiki/Dominator_(graph_theory)
    """

    dominators = g1.compute_dominators(1)
    assert (dominators == {1: set([1]),
                           2: set([1, 2]),
                           3: set([1, 2, 3]),
                           4: set([1, 2, 4]),
                           5: set([1, 2, 5]),
                           6: set([1, 2, 6])})

    assert (list(g1.walk_dominators(1, dominators)) == [])
    assert (list(g1.walk_dominators(2, dominators)) == [1])
    assert (list(g1.walk_dominators(3, dominators)) == [2, 1])
    assert (list(g1.walk_dominators(4, dominators)) == [2, 1])
    assert (list(g1.walk_dominators(5, dominators)) == [2, 1])
    assert (list(g1.walk_dominators(6, dominators)) == [2, 1])


@pytest.fixture
def g2():
    g2 = DiGraph()
    g2.add_edge(1, 2)
    g2.add_edge(2, 3)
    g2.add_edge(3, 4)
    g2.add_edge(5, 6)
    g2.add_edge(6, 3)
    g2.add_edge(4, 7)
    g2.add_edge(4, 8)
    g2.add_edge(7, 9)
    g2.add_edge(8, 9)
    return g2


def test_multiple_heads(g2):
    dominators = g2.compute_dominators(5)
    assert (dominators == {3: set([3, 5, 6]),
                           4: set([3, 4, 5, 6]),
                           5: set([5]),
                           6: set([5, 6]),
                           7: set([3, 4, 5, 6, 7]),
                           8: set([3, 4, 5, 6, 8]),
                           9: set([3, 4, 5, 6, 9])})

    assert (list(g2.walk_dominators(1, dominators)) == [])
    assert (list(g2.walk_dominators(2, dominators)) == [])
    assert (list(g2.walk_dominators(3, dominators)) == [6, 5])
    assert (list(g2.walk_dominators(4, dominators)) == [3, 6, 5])
    assert (list(g2.walk_dominators(5, dominators)) == [])
    assert (list(g2.walk_dominators(6, dominators)) == [5])
    assert (list(g2.walk_dominators(7, dominators)) == [4, 3, 6, 5])
    assert (list(g2.walk_dominators(8, dominators)) == [4, 3, 6, 5])
    assert (list(g2.walk_dominators(9, dominators)) == [4, 3, 6, 5])


def test_postdominators_g1_6(g1):
    postdominators = g1.compute_postdominators(6)
    assert (postdominators == {1: set([1, 2, 6]),
                               2: set([2, 6]),
                               3: set([2, 3, 5, 6]),
                               4: set([2, 4, 5, 6]),
                               5: set([2, 5, 6]),
                               6: set([6])})

    assert (list(g1.walk_postdominators(1, postdominators)) == [2, 6])
    assert (list(g1.walk_postdominators(2, postdominators)) == [6])
    assert (list(g1.walk_postdominators(3, postdominators)) == [5, 2, 6])
    assert (list(g1.walk_postdominators(4, postdominators)) == [5, 2, 6])
    assert (list(g1.walk_postdominators(5, postdominators)) == [2, 6])
    assert (list(g1.walk_postdominators(6, postdominators)) == [])


def test_postdominators_g1_5(g1):
    postdominators = g1.compute_postdominators(5)
    assert (postdominators == {1: set([1, 2, 5]),
                               2: set([2, 5]),
                               3: set([3, 5]),
                               4: set([4, 5]),
                               5: set([5])})

    assert (list(g1.walk_postdominators(1, postdominators)) == [2, 5])
    assert (list(g1.walk_postdominators(2, postdominators)) == [5])
    assert (list(g1.walk_postdominators(3, postdominators)) == [5])
    assert (list(g1.walk_postdominators(4, postdominators)) == [5])
    assert (list(g1.walk_postdominators(5, postdominators)) == [])
    assert (list(g1.walk_postdominators(6, postdominators)) == [])


def test_postdominators_g2_4(g2):
    postdominators = g2.compute_postdominators(4)
    assert (postdominators == {1: set([1, 2, 3, 4]),
                               2: set([2, 3, 4]),
                               3: set([3, 4]),
                               4: set([4]),
                               5: set([3, 4, 5, 6]),
                               6: set([3, 4, 6])})

    assert (list(g2.walk_postdominators(1, postdominators)) == [2, 3, 4])
    assert (list(g2.walk_postdominators(2, postdominators)) == [3, 4])
    assert (list(g2.walk_postdominators(3, postdominators)) == [4])
    assert (list(g2.walk_postdominators(4, postdominators)) == [])
    assert (list(g2.walk_postdominators(5, postdominators)) == [6, 3, 4])
    assert (list(g2.walk_postdominators(6, postdominators)) == [3, 4])
    assert (list(g2.walk_postdominators(7, postdominators)) == [])
    assert (list(g2.walk_postdominators(8, postdominators)) == [])
    assert (list(g2.walk_postdominators(9, postdominators)) == [])


def test_immediate_dominators_g1_1(g1):
    idoms = g1.compute_immediate_dominators(1)
    assert (idoms == {2: 1,
                      3: 2,
                      4: 2,
                      5: 2,
                      6: 2})


def test_immediate_dominators_g2_1(g2):
    idoms = g2.compute_immediate_dominators(1)
    assert (idoms == {2: 1,
                      3: 2,
                      4: 3,
                      7: 4,
                      8: 4,
                      9: 4})


def test_immediate_dominators_g2_5(g2):
    idoms = g2.compute_immediate_dominators(5)
    assert (idoms == {3: 6,
                      4: 3,
                      6: 5,
                      7: 4,
                      8: 4,
                      9: 4})


def test_frontier_g1_1(g1):
    frontier = g1.compute_dominance_frontier(1)
    assert (frontier == {2: set([2]),
                         3: set([5]),
                         4: set([5]),
                         5: set([2])})


def test_frontier_g2_1(g2):
    frontier = g2.compute_dominance_frontier(1)
    assert (frontier == {7: set([9]),
                         8: set([9])})


def test_frontier_g2_5(g2):
    frontier = g2.compute_dominance_frontier(5)
    assert (frontier == {7: set([9]),
                         8: set([9])})


@pytest.fixture
def g3():
    g3 = DiGraph()
    g3.add_edge(1, 2)
    g3.add_edge(1, 3)
    g3.add_edge(2, 4)
    g3.add_edge(2, 5)
    g3.add_edge(3, 7)
    g3.add_edge(3, 8)
    g3.add_edge(4, 9)
    g3.add_edge(5, 9)
    g3.add_edge(7, 6)
    g3.add_edge(8, 6)
    g3.add_edge(9, 6)
    g3.add_edge(9, 2)
    g3.add_edge(9, 1)
    g3.add_edge(7, 8)
    g3.add_edge(8, 7)
    return g3


def test_natural_loops(g3):
    loops = set([(backedge, frozenset(body)) for backedge, body in g3.compute_natural_loops(1)])
    assert (loops == {((9, 1), frozenset({1, 2, 4, 5, 9})),
                      ((9, 2), frozenset({2, 4, 5, 9}))})


def test_irreducible_loops(g3):
    sccs = set([frozenset(scc) for scc in g3.compute_strongly_connected_components()])
    assert (sccs == {frozenset({6}),
                 frozenset({7, 8}),
                 frozenset({3}),
                 frozenset({1, 2, 4, 5, 9})})


@pytest.fixture
def graph():
    graph = DiGraph()
    graph.add_edge(1, 2)
    graph.add_edge(2, 3)
    return graph


@pytest.fixture
def graph2():
    graph2 = DiGraph()
    graph2.add_edge(2, 3)
    graph2.add_edge(1, 2)
    return graph2


def test_equality(graph, graph2):
    assert graph == graph2


def test_copy(graph):
    graph4 = graph.copy()
    assert graph == graph4


def test_merge(graph):
    graph4 = graph.copy()

    graph3 = DiGraph()
    graph3.add_edge(3, 1)
    graph3.add_edge(1, 4)
    graph4 += graph3
    for node in graph3.nodes():
        assert node in graph4.nodes()
    for edge in graph3.edges():
        assert edge in graph4.edges()
    assert graph4.nodes() == graph.nodes().union(graph3.nodes())
    assert sorted(graph4.edges()) == sorted(graph.edges() + graph3.edges())


def test_matcher_str():
    j1 = MatchGraphJoker(name="dad")
    j2 = MatchGraphJoker(name="son")
    print(j1 >> j2 >> j1)


def test_ensure_form():
    j1 = MatchGraphJoker(name="dad")
    j2 = MatchGraphJoker(name="son")
    matcher = j1 >> j2 >> j1

    assert isinstance(matcher, MatchGraph)
    assert len(matcher.nodes()) == 2
    assert len(matcher.edges()) == 2


@pytest.fixture
def simple_graph():
    graph = DiGraph()
    graph.add_edge(1, 2)
    graph.add_edge(2, 1)
    graph.add_edge(2, 3)
    return graph


def test_match_simple(simple_graph):
    j1 = MatchGraphJoker(name="dad")
    j2 = MatchGraphJoker(name="son")
    matcher = j1 >> j2 >> j1

    sols = list(matcher.match(simple_graph))
    assert len(sols) == 0


def test_modify_restrictions(simple_graph):
    j1 = MatchGraphJoker(name="dad")
    j2 = MatchGraphJoker(name="son", restrict_out=False)
    matcher = j1 >> j2 >> j1

    sols = list(matcher.match(simple_graph))
    assert len(sols) == 1
    assert sols[0] == {j1: 1,
                       j2: 2}


def test_solution_combinaison(simple_graph):
    j1 = MatchGraphJoker(name="dad", restrict_out=False)
    j2 = MatchGraphJoker(name="son", restrict_out=False)
    matcher = j1 >> j2 >> j1

    sols = list(matcher.match(simple_graph))
    assert len(sols) == 2
    assert len([sol for sol in sols if sol[j1] == 1]) == 1
    assert len([sol for sol in sols if sol[j1] == 2]) == 1


def test_filter(simple_graph):
    j1 = MatchGraphJoker(name="dad", restrict_out=False)
    j2 = MatchGraphJoker(name="son", restrict_out=False, filt=lambda graph, node: node < 2)
    matcher = j1 >> j2 >> j1

    sols = list(matcher.match(simple_graph))
    assert len(sols) == 1
    assert sols[0] == {j1: 2,
                       j2: 1}


def test_add():
    j1 = MatchGraphJoker(name="dad")
    j2 = MatchGraphJoker(name="son")
    j3 = MatchGraphJoker(name="sonson", restrict_in=False)
    matcher = j1 >> j2
    matcher += j2 >> j3
    assert isinstance(matcher, MatchGraph)
    assert len(matcher.nodes()) == 3
    assert len(matcher.edges()) == 2


def test_restrict_in():
    j1 = MatchGraphJoker(name="dad")
    j2 = MatchGraphJoker(name="son")
    j3 = MatchGraphJoker(name="sonson", restrict_in=False)
    matcher = j1 >> j2
    matcher += j2 >> j3

    graph = DiGraph()
    graph.add_edge(1, 2)
    graph.add_edge(2, 3)
    graph.add_edge(4, 3)
    sols = list(matcher.match(graph))
    assert len(sols) == 1
    assert sols[0] == {j1: 1,
                       j2: 2,
                       j3: 3}


def test_compute_weakly_connected_components():
    graph = DiGraph()
    graph.add_edge(1, 2)
    graph.add_edge(2, 2)
    graph.add_edge(3, 4)

    components = graph.compute_weakly_connected_components()
    assert sorted(components) == [set([1, 2]), set([3, 4])]
