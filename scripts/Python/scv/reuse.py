import pandas as pd
import numpy as np
import seaborn as sb
import matplotlib.pyplot as plt
import sys

FILE = sys.argv[1]
BENCH_FILE = sys.argv[2]

df = pd.read_csv(FILE)
df_bench = pd.read_csv(BENCH_FILE)[["name", "scvFunctionSummariesTopSort_time", "scvRktFsR_time", "scvFunctionSummariesTopSort_# components", "scvRktFsR_# components"]]
df_bench_named = df_bench.set_index("name")
df_bench_named["speedup"] =  df_bench_named["scvRktFsR_time"].replace(["_", "TIMEOUT"], np.Inf).astype(float) / df_bench_named["scvFunctionSummariesTopSort_time"].replace(["_", "TIMEOUT"], 1).astype(float)
print(df.groupby("name").sum()["metric"] / df_bench.set_index("name")["scvFunctionSummariesTopSort_# components"])
df_bench_named["reuse"] = df.groupby("name").sum()["metric"].astype(float) / df_bench_named["scvFunctionSummariesTopSort_# components"].astype(float)
df_bench_named["component_reduction"] = 1 - df_bench_named["scvFunctionSummariesTopSort_# components"] / df_bench_named["scvRktFsR_# components"].replace(["_", "TIMEOUT"], 1.0).astype(float)
df_bench_named["got_speedup"] = df_bench_named["speedup"] > 1
df_bench_with_speedup = df_bench_named.where(df_bench_named["component_reduction"] > -8).dropna()
print(df_bench_with_speedup)

# 1 row, 2 columns
figure, axes = plt.subplots(2, 2, sharex=False, sharey=False)
figure.suptitle("Performance")

sb.scatterplot(ax = axes[0][0], data = df_bench_with_speedup, x = "reuse", y = "speedup", hue = "got_speedup")
sb.scatterplot(ax = axes[0][1], data = df_bench_with_speedup, x = "component_reduction", y = "speedup", hue = "got_speedup")
sb.displot(ax = axes[1][0], data = df_bench_with_speedup, x = "component_reduction", hue = "got_speedup")
plt.show()
