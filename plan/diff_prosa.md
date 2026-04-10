## Prosa と本プロジェクトの差分

### 1. 主目標の違い

* **Prosa**
  主目標は、**機械検証された real-time schedulability analysis の共有基盤**を作ることにある。Prosa 自身が “A Foundation for Formally Proven Schedulability Analysis” を掲げており、Goals でも **trustworthy schedulability analysis** を中心に、**研究者向け**で、**十分条件を優先**すると明示している。 ([Prosa][1])

* **本プロジェクト**
  主目標は、**実行可能な scheduler semantics の定式化**と、**abstract policy と concrete dispatcher の refinement** を中心に据え、そこから **single-CPU → multicore → OS semantics** へ伸ばすことにある。現在のロードマップでも、共通基盤・dispatch 抽象・single-CPU bridge・EDF/FIFO・partitioned 基盤・periodic task 骨格を土台にしつつ、次の中核を **single-CPU scheduler semantics / dispatcher refinement / EDF 最適性 / multicore / OS model** に置いている。

---

### 2. 重心の違い

* **Prosa の重心**
  Prosa の公開成果は、EDF/FP/ELF/FIFO などに関する **optimality / generality / response-time analysis** が厚く、特に現行の公開構成では **priority / schedule / preemption / workload / interference / busy interval / RTA** の層が非常に充実している。 ([Prosa][2])

* **本プロジェクトの重心**
  本プロジェクトでは、解析結果そのものを増やすよりも、まず

  * policy
  * scheduler validity
  * dispatcher
  * dispatcher refinement
    を切り分け、そのうえで **EDF 最適性を「実行可能な chooser まで接続した理論」**として仕上げることを重視する。さらに multicore でも、最初に扱うのは **RTA** ではなく **partitioned / global / clustered / affinity / migration の意味論** である。

---

### 3. 「何を中心概念にするか」の違い

* **Prosa**
  中心概念は、**schedulability analysis を支えるモデルと解析補題**である。公開 ToC を見ると、`model.priority.*`、`model.schedule.*`、`analysis.definitions.*`、`analysis.abstract.*`、`results.rta.*` が大きな柱になっている。 ([Prosa][2])

* **本プロジェクト**
  中心概念は、**scheduler そのものの意味論**である。
  具体的には、

  * `PriorityPolicy`
  * `SchedulerValidity`
  * `DispatcherRefinement`
  * `ScheduleTransform`
    のような層を前面に出し、**「どの schedule が policy を満たすか」**と **「どの dispatcher がその policy を実装するか」**を主役にする。

---

### 4. refinement の位置づけの違い

* **Prosa**
  Prosa にも `implementation.refinements.*` は存在するため、refinement 自体がないわけではない。だが、公開されている全体構成では、refinement はライブラリの一部であり、プロジェクト全体の主看板はあくまで **schedulability analysis** である。 ([Prosa][3])

* **本プロジェクト**
  refinement は補助層ではなく、**中心目標の一つ**である。
  つまり、

  * `choose_edf` が EDF policy を実装する
  * local dispatcher refinement から global/partitioned refinement を導く
  * 将来的には kernel scheduler 実装が abstract scheduler spec を満たす
    という方向が最初からロードマップに入っている。

---

### 5. EDF の扱いの違い

* **Prosa**
  Prosa にはすでに **EDF Priority Policy**、**EDF Schedules**、さらに **Optimality of EDF on Ideal Uniprocessors** がある。つまり EDF 自体は十分に扱われている。 ([Prosa][2])

* **本プロジェクト**
  EDF は単なる既存結果の再形式化ではなく、

  * finite candidate ベース
  * tie を含む executable chooser
  * schedule transform / swap 補題
  * dispatcher refinement
    に接続した形で仕上げる。
    したがって、差分は「EDF を扱うかどうか」ではなく、**EDF をどの層まで貫いて mechanize するか**にある。

---

### 6. multicore の扱いの違い

* **Prosa**
  Prosa は multiprocessor scheduling を全く扱わないわけではない。results ページには **Classic Prosa** 側として G-EDF などの multiprocessor results も見える。だが、現行の mainline の印象としては、公開成果の前面には uniprocessor とその解析系が強く出ている。 ([Prosa][4])

* **本プロジェクト**
  multicore は「後で解析を付ける対象」ではなく、**早い段階から意味論として入れる対象**である。
  特にロードマップでは、

  * `Partitioned.v`
  * `Global.v`
  * `Clustered.v`
  * `Affinity.v`
  * `Migration.v`
    という順で、**partitioned / global / clustered / affinity / migration** を同一の `Schedule` 抽象上に載せることを目指している。

---

### 7. OS への伸ばし方の違い

* **Prosa**
  Prosa は real-time scheduling theory の共有基盤として非常に強いが、Goals でも **研究者向けであり、end users 向けではない**と明示されている。つまり、日常的な OS scheduler 実装の直接表現は主戦場ではない。 ([Prosa][5])

* **本プロジェクト**
  本プロジェクトは、将来的に

  * runqueue
  * current task
  * wakeup / block / completion
  * dispatch point / preemption point
  * migration event
  * timer / IPI
    といった **OS 寄り operational semantics** へ伸ばすことを、明示的な phase として持っている。ここは Prosa との最も大きな差分の一つである。

---

### 8. task model / analysis の位置づけの違い

* **Prosa**
  task model は analysis の前提としてかなり豊富に整備されており、その上で DBF, interference, busy interval, RTA などへ進む構成になっている。 ([Prosa][2])

* **本プロジェクト**
  periodic / sporadic task model は本体ではなく、**scheduler semantics に接続する adapter** として後段に置く。
  つまり、task model は「理論の中心」ではなく、「scheduler semantics の上位層」として扱う方針である。

---

### 9. 一言でまとめた差分

* **Prosa** は
  **「検証済み schedulability analysis の共有基盤」** である。 ([Prosa][1])

* **本プロジェクト** は
  **「実行可能な scheduler semantics と dispatcher refinement の共有基盤」** を目指している。そこから **single-CPU → multicore → OS semantics** へ伸ばす。

---

### 10. コア差分だけを箇条書きで抜くと

* Prosa は **analysis-centered**、本プロジェクトは **semantics/refinement-centered**
* Prosa は **研究者向け schedulability analysis** が主目的、本プロジェクトは **scheduler / dispatcher の mechanized semantics** が主目的
* Prosa でも refinement はあるが、本プロジェクトでは refinement が **主役**
* Prosa でも EDF optimality はあるが、本プロジェクトでは EDF を **executable dispatcher まで貫く**
* Prosa でも multiprocessor はあるが、本プロジェクトでは multicore を **意味論の中心テーマ**として早期に扱う
* 本プロジェクトはさらに **OS 寄り operational model** への拡張を明示的に持つ

必要なら次に、これをそのまま `README` や `roadmap.md` に貼れるように、もっと短い版に圧縮します。

[1]: https://prosa.mpi-sws.org/?utm_source=chatgpt.com "Prosa: A Foundation for Formally Proven Schedulability Analysis"
[2]: https://prosa.mpi-sws.org/branches/master/pretty/toc.html?utm_source=chatgpt.com "Table of Contents"
[3]: https://prosa.mpi-sws.org/branches/prepare_MC_PR/pretty/toc.html?utm_source=chatgpt.com "Table of Contents"
[4]: https://prosa.mpi-sws.org/results.html?utm_source=chatgpt.com "Overview of Verified Results"
[5]: https://prosa.mpi-sws.org/goals-and-principles.html?utm_source=chatgpt.com "Goals and Principles"
