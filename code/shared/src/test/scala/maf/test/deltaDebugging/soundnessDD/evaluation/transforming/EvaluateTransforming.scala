package maf.test.deltaDebugging.soundnessDD.evaluation.transforming

import maf.test.deltaDebugging.soundnessDD.evaluation.Evaluate
import maf.util.benchmarks.Statistics

object SaveTransforming:
  def save(): Unit = {
    Evaluate.save(
      List(
        new SchemeModFLocalAdaptiveTests1,
        new SchemeModFLocalAdaptiveTests2,
        new SchemeModFLocalAdaptiveTests3,
        new SchemeModFLocalAdaptiveTests4,
        new SchemeModFLocalAdaptiveTests5,
        new SchemeModFLocalAdaptiveTests6,
        new SchemeModFLocalAdaptiveTests7,
        new SchemeModFLocalAdaptiveTests8,
      ),
      "transformingDataCollector",
      TransformingDD.dataCollector
    )
  }

object ReadAndAnalyzeTransforming:
  def main(args: Array[String]): Unit = {
    Evaluate.readAndAnalyzeData(
      "transformingDataCollector"
    )
  }

