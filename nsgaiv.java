package com.assembly.algorithm;

import static org.moeaframework.core.NondominatedSorting.RANK_ATTRIBUTE;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.moeaframework.algorithm.AbstractEvolutionaryAlgorithm;
import org.moeaframework.core.EpsilonBoxDominanceArchive;
import org.moeaframework.core.Initialization;
import org.moeaframework.core.NondominatedSorting;
import org.moeaframework.core.NondominatedSortingPopulation;
import org.moeaframework.core.Population;
import org.moeaframework.core.Problem;
import org.moeaframework.core.Selection;
import org.moeaframework.core.Solution;
import org.moeaframework.core.Variation;
import org.moeaframework.core.comparator.ChainedComparator;
import org.moeaframework.core.comparator.CrowdingComparator;
import org.moeaframework.core.comparator.RankComparator;
import org.moeaframework.core.operator.TournamentSelection;
import org.moeaframework.core.variable.EncodingUtils;

public class nsgaiv extends AbstractEvolutionaryAlgorithm {

	private Variation variation;
	private Selection selection;

	public nsgaiv(Problem problem, NondominatedSortingPopulation population,
			EpsilonBoxDominanceArchive archive, Variation variation, Initialization initialization) {
		// TODO Auto-generated constructor stub
		super(problem, population, archive, initialization);

		// define the selection operator,二元锦标赛选择
		selection = new TournamentSelection(2, new ChainedComparator(new RankComparator(), new CrowdingComparator()));
		this.variation = variation;
	}

	@Override
	protected void iterate() {
		// TODO Auto-generated method stub

		// get the current population
		NondominatedSortingPopulation population = (NondominatedSortingPopulation) getPopulation();
		// 修改
		EpsilonBoxDominanceArchive archive = (EpsilonBoxDominanceArchive) getArchive();
		Population offspring = new Population();
		int populationSize = population.size();

		// run NSGA-II using selection with replacement; this version allows
		// using custom selection operators
		while (offspring.size() < populationSize) {
			// 从pop(t)中选择2个个体
			Solution[] parents = selection.select(variation.getArity(), population);

			// 交叉、变异后的个体纳入offspring(t)
			offspring.addAll(variation.evolve(parents));
		}

		// 适应度评估
		evaluateAll(offspring);

		if (archive != null) {
			archive.addAll(offspring);
		}

		Population data_all = new Population();
		offspring.forEach(child -> data_all.add(child));
		population.forEach(parent -> data_all.add(parent));
		population.clear();

		// 计算多目标指标，非支配排序估计
		NondominatedSorting nondominatedSorting = new NondominatedSorting();
		nondominatedSorting.evaluate(data_all);

		Map<Integer, Set<Solution>> data_NondominatedSorting = new HashMap<Integer, Set<Solution>>();
		for (Solution solution : data_all) {
			int rank = (Integer) solution.getAttribute(RANK_ATTRIBUTE);
			if (data_NondominatedSorting.get(rank) == null) {
				Set<Solution> solutionSet = new HashSet<Solution>();
				data_NondominatedSorting.put(rank, solutionSet);
			}
			data_NondominatedSorting.get(rank).add(solution);
		}

		Population data_P_R = new Population();
		int rank = 0;
		while (data_P_R.size() + data_NondominatedSorting.get(rank).size() <= 0.5 * populationSize) {
			data_NondominatedSorting.get(rank).stream().forEach(solution -> solution.setAttribute("subarea", "Q1"));
			data_P_R.addAll(data_NondominatedSorting.get(rank));
			rank++;
		}

		do {
			data_NondominatedSorting.get(rank).stream().forEach(solution -> solution.setAttribute("subarea", "Q2"));
			data_P_R.addAll(data_NondominatedSorting.get(rank));
			rank++;
		} while (data_P_R.size() < 1.5 * populationSize);

		Double[][] wed = new Double[data_P_R.size()][data_P_R.size()];
		for (int i = 0; i < data_P_R.size(); i++) {
			wed[i][i] = 0.0;
			for (int j = i + 1; j < data_P_R.size(); j++) {
				Double wedValue = this.calWeightedEuclideanDistance(data_P_R.get(i), data_P_R.get(j));
				wed[i][j] = wedValue;
				wed[j][i] = wedValue;
			}
		}

		// 记录移除个体的索引
		List<Integer> removeIndexs = new ArrayList<Integer>();
		while (data_P_R.size() - removeIndexs.size() > populationSize) {
			// 找出距离最近的两个簇c_i 和c_j ，且c_i和c_j至少有一个属于Q2
			Double minDistance = Double.MAX_VALUE;
			int min_i = 0;
			int min_j = 0;
			for (int i = 0; i < data_P_R.size(); i++) {
				if (removeIndexs.contains(i)) {
					continue;
				}
				for (int j = i + 1; j < data_P_R.size(); j++) {
					if (removeIndexs.contains(j)) {
						continue;
					}

					if ("Q1".equals(data_P_R.get(i).getAttribute("subarea"))
							&& "Q1".equals(data_P_R.get(j).getAttribute("subarea"))) {
						continue;
					}
					if (minDistance.compareTo(wed[i][j]) == 1) {
						minDistance = wed[i][j];
						min_i = i;
						min_j = j;
					}

				}
			}

			if ("Q2".equals(data_P_R.get(min_i).getAttribute("subarea"))
					&& "Q2".equals(data_P_R.get(min_j).getAttribute("subarea"))) {
				// 计算d(c_i)和d(c_j)
				Double minDistance_i = this.calculateMinDistance(wed, removeIndexs, min_i, min_j);
				Double minDistance_j = this.calculateMinDistance(wed, removeIndexs, min_j, min_i);
				if (minDistance_i.compareTo(minDistance_j) == -1) {
					removeIndexs.add(min_i);
				} else {
					removeIndexs.add(min_j);
				}
			} else if ("Q1".equals(data_P_R.get(min_i).getAttribute("subarea"))
					&& "Q2".equals(data_P_R.get(min_j).getAttribute("subarea"))) {
				removeIndexs.add(min_j);
			} else if ("Q2".equals(data_P_R.get(min_i).getAttribute("subarea"))
					&& "Q1".equals(data_P_R.get(min_j).getAttribute("subarea"))) {
				removeIndexs.add(min_i);
			}
		}

		// 迭代移除
		for (int i = 0; i < data_P_R.size(); i++) {
			if (removeIndexs.contains(i)) {
				continue;
			}
			population.add(data_P_R.get(i));
		}
		data_P_R.clear();
		data_all.clear();
		removeIndexs.clear();
	}

	private Double calculateMinDistance(Double[][] wed, List<Integer> removeIndexs, int min_i, int min_j) {
		// TODO Auto-generated method stub
		Double minDistance = Double.MAX_VALUE;
		for (int k = 0; k < wed.length; k++) {
			if (removeIndexs.contains(k) || k == min_i || k == min_j) {
				continue;
			}
			if (minDistance.compareTo(wed[min_i][k]) == 1) {
				minDistance = wed[min_i][k];
			}
		}
		return minDistance;
	}

	private Double calWeightedEuclideanDistance(Solution solution_i, Solution solution_j) {
		// TODO Auto-generated method stub

		int K = solution_i.getNumberOfVariables();
		Double value = 0.0;

		// the encode solution is composed by some real values. 
		for (int k = 0; k < K; k++) {
			double code_i = EncodingUtils.getReal(solution_i.getVariable(k));
			double code_j = EncodingUtils.getReal(solution_j.getVariable(k));

			value += Math.pow(code_i - code_j, 2);
		}

		return Math.sqrt(value);
	}

	@Override
	public EpsilonBoxDominanceArchive getArchive() {
		return (EpsilonBoxDominanceArchive) super.getArchive();
	}

	@Override
	public NondominatedSortingPopulation getPopulation() {
		return (NondominatedSortingPopulation) super.getPopulation();
	}

}
