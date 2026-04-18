design/Foundation.md は現状の theories/Foundation/Base.v / Arithmetic.v の範囲をおおむね正しく説明している。
 
 ただし、実装コメントや定義と比べると、文書としては数点の抜け漏れがある。
 
 抜けている／薄い点
 
 1. Schedule が CPU 数を内包しないこと
 
 Base.v の Schedule は次である。
 
 Definition Schedule : Type := Time -> CPU -> option JobId.
 
 つまり、m : nat のような CPU 数は Schedule 型には入っていない。
 有限CPU範囲 c < m や valid_schedule jobs m sched は上位層で扱う。
 
 Foundation.md には「multicore-capable」とあるが、CPU boundedness は Foundation では保証しないという点を明記した方がよい。
 
 2. Job の job_task = 0 慣習
 
 実装コメントでは job_task に
 
 (* which task generated this job (0 = anonymous) *)
 
 という慣習がある。
 
 Foundation.md は job_task を列挙しているだけで、standalone job / anonymous job を 0 で表す現在の慣習を説明していない。
 
 3. job_index の意味
 
 実装では job_index は
 
 (* k-th job of that task, 0-indexed (instance number) *)
 
 である。
 
 Foundation.md では job_index の存在は書いてあるが、0-indexed instance number であることは抜けている。
 周期・sporadic・jittered task model で使うので、追記した方がよい。
 
 4. valid_jobs の意味が薄い
 
 実装では
 
 Definition valid_jobs (jobs : JobId -> Job) : Prop :=
   forall j, 0 < job_cost (jobs j).
 
 であり、すべての job が正の cost を持つという述語である。
 
 さらにコメントでは、zero-cost job は t = 0 で即 completed になるため ready/eligible 論理で注意が必要、と説明している。
 
 Foundation.md は valid_jobs を名前として挙げているだけなので、最低限
 
 * valid_jobs は positive job cost を要求する
 * zero-cost job は Foundation では許されるが、valid_jobs で除外される
 * positivity は record invariant ではなく述語で表す
 
 を明記すべきである。
 
 5. pre_release が「waiting」ではないこと
 
 実装コメントでは、pre_release は
 
 t < job_release (jobs j)
 
 であり、ready queue 上の waiting とは違う、と明示している。
 
 Foundation.md では pre_release の名前だけなので、“not yet released” であり “waiting in ready queue” ではないと書くと誤解が減る。
 
 6. valid_job_of_task の正確な中身
 
 Foundation.md は「job と task を data level で関係づける」と書いているが、実装上の中身は次の2条件だけである。
 
 job_abs_deadline (jobs j) =
   job_release (jobs j) + task_relative_deadline (tasks τ)
 /\
 job_cost (jobs j) <= task_cost (tasks τ)
 
 したがって、文書にも
 
 * absolute deadline = release + relative deadline
 * job cost <= task WCET
 * release pattern は含まない
 * job_index の一意性は含まない
 * period spacing は含まない
 
 を明記した方がよい。
 
 7. Task record 自体には positivity invariant がないこと
 
 Task は
 
 task_cost : nat
 task_period : nat
 task_relative_deadline : nat
 
 だけであり、0 < task_period や 0 < task_cost は record には入っていない。
 
 Foundation.md には「minimal」とあるので方向性は合っているが、period/cost/deadline の妥当性は task-model 層の述語で扱うと追記するとよい。
 
 8. DAG 拡張方針の具体性
 
 Foundation.md には DAG-aware execution units への拡張余地は書かれている。
 ただし、実装コメントにはより具体的に
 
 * Task
 * Job
 * Node
 
 の3層化、および将来の Schedule が
 
 Time -> CPU -> option NodeId
 
 または
 
 Time -> CPU -> option (JobId * NodeId)
 
 へ移る可能性が書かれている。
 
 これは Foundation の将来互換性に関わるので、文書にも入れてよい。
 
 9. Arithmetic.v の具体的な公開補題名
 
 Foundation.md は arithmetic lemmas とだけ書いているが、現状の公開補題は次の4つである。
 
 nat_div2_double
 nat_div2_succ_double
 nat_div_mul_exact
 nat_mod_mul_left
 
 設計文書として網羅性を上げるなら、File map か Core concepts に列挙するとよい。
 
 逆に、問題なさそうな点
 
 以下は現状実装と整合している。
 
 * Foundation の対象が Base.v と Arithmetic.v に限定されている点
 * JobId / TaskId / CPU / Time がすべて nat である点
 * Task / Job が最小 record である点
 * Schedule が multicore 形状である点
 * eligible / ready / completed / valid_schedule を Foundation に入れない設計
 * periodic / sporadic / jittered generation を Foundation に入れない設計
 * operational trace や refinement を Foundation に入れない設計
 
 推奨TODO
 
 design/Foundation.md に次の追記を行うのがよい。
 
 1. Schedule は raw carrier であり、CPU 数 m や c < m は上位層の責務である、と追記する。
 2. Job の job_task = 0 anonymous convention と job_index の 0-indexed instance number を追記する。
 3. valid_jobs の定義を positive cost invariant として明記する。
 4. pre_release は ready-queue waiting ではない、と明記する。
 5. valid_job_of_task の2条件と、含まない条件を明記する。
 6. Task record 自体は positivity を保証しない、と明記する。
 7. DAG 拡張方針を Task / Job / Node の3層として具体化する。
 8. Arithmetic.v の4補題名を列挙する。
