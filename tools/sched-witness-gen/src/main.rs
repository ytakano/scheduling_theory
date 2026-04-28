use clap::{Parser, Subcommand};
use rayon::ThreadPoolBuilder;
use rayon::prelude::*;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::cmp::Ordering;
use std::fs;
use std::path::PathBuf;

const MAX_HORIZON: u64 = 200_000;
const MAX_BASIS_JOBS: usize = 200_000;
const MAX_JITTERED_DBF_WINDOWS: usize = 200_000;

#[derive(Parser)]
#[command(name = "sched-witness-gen")]
#[command(about = "Generate schedulability witnesses checked by extracted Haskell")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    PeriodicEdf(PeriodicEdfArgs),
    JitteredPeriodicEdf(JitteredPeriodicEdfArgs),
}

#[derive(Parser)]
struct PeriodicEdfArgs {
    #[arg(long)]
    tasks: PathBuf,
    #[arg(long)]
    out: PathBuf,
    #[arg(long, default_value = "auto")]
    threads: String,
    #[arg(long)]
    metrics_out: Option<PathBuf>,
}

#[derive(Parser)]
struct JitteredPeriodicEdfArgs {
    #[arg(long)]
    tasks: PathBuf,
    #[arg(long)]
    out: PathBuf,
    #[arg(long, default_value = "auto")]
    threads: String,
}

#[derive(Clone, Debug)]
struct Task {
    cost: u64,
    period: u64,
    deadline: u64,
    offset: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct JitteredTask {
    cost: u64,
    period: u64,
    deadline: u64,
    offset: u64,
    jitter: u64,
}

#[derive(Clone, Debug)]
struct Job {
    id: u64,
    task: usize,
    index: u64,
    release: u64,
    cost: u64,
    deadline: u64,
}

#[derive(Serialize)]
struct Witness {
    schema_version: u64,
    policy: &'static str,
    domain: &'static str,
    task_hash: String,
    generator: GeneratorInfo,
    cert: Cert,
    sidecar: Sidecar,
    generator_stats: GeneratorStats,
}

#[derive(Debug, Serialize)]
struct GeneratorInfo {
    name: &'static str,
    version: &'static str,
}

#[derive(Serialize)]
struct Cert {
    prefix: PrefixCert,
    transport: TransportCert,
    dbf: DbfCert,
}

#[derive(Serialize)]
struct PrefixCert {
    horizon: u64,
    basis_jobs: Vec<u64>,
    slots: Vec<Option<u64>>,
    completed_by: Vec<u64>,
    backlog_free_matrix: Vec<Vec<bool>>,
}

#[derive(Serialize)]
struct TransportCert {
    period: u64,
    basis_jobs: Vec<u64>,
    classes: Vec<TransportClass>,
    job_class: Vec<u64>,
    job_shift: Vec<u64>,
}

#[derive(Serialize)]
struct TransportClass {
    rep_job: u64,
    completion_offset: u64,
    backlog_offset: u64,
}

#[derive(Serialize)]
struct DbfCert {
    cutoff: u64,
    ok_table: Vec<bool>,
}

#[derive(Serialize)]
struct Sidecar {
    candidate_jobs: Vec<u64>,
    class_relevant_jobs: Vec<Vec<u64>>,
    window_target_certs: Vec<WindowTargetCert>,
    post_reset_window_target_certs: Vec<WindowTargetCert>,
}

#[derive(Serialize)]
struct WindowTargetCert {
    target_job: u64,
    class_id: u64,
    shift: u64,
    pairs: Vec<WindowPairCert>,
}

#[derive(Serialize)]
struct WindowPairCert {
    target_earlier_job: u64,
    rep_earlier_job: u64,
    delta: u64,
}

#[derive(Serialize)]
struct GeneratorStats {
    task_count: usize,
    prefix_horizon: u64,
    prefix_job_count: usize,
    transport_basis_job_count: usize,
    window_target_count: usize,
    post_reset_window_target_count: usize,
    thread_mode: String,
}

#[derive(Debug, Serialize)]
struct JitteredWitness {
    schema_version: u64,
    policy: &'static str,
    domain: &'static str,
    task_hash: String,
    generator: GeneratorInfo,
    cert: JitteredCert,
    generator_stats: JitteredGeneratorStats,
}

#[derive(Debug, Serialize)]
struct JitteredCert {
    dbf: JitteredDbfCert,
}

#[derive(Debug, Serialize)]
struct JitteredDbfCert {
    cutoff: u64,
    checked_windows: Vec<[u64; 2]>,
    all_windows_checked: bool,
}

#[derive(Debug, Serialize)]
struct JitteredGeneratorStats {
    task_count: usize,
    cutoff: u64,
    checked_window_count: usize,
    thread_mode: String,
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let cli = Cli::parse();
    match cli.command {
        Command::PeriodicEdf(args) => run_periodic_edf(args),
        Command::JitteredPeriodicEdf(args) => run_jittered_periodic_edf(args),
    }
}

fn run_periodic_edf(args: PeriodicEdfArgs) -> Result<(), String> {
    let thread_mode = ThreadMode::parse(&args.threads)?;

    let csv = fs::read_to_string(&args.tasks)
        .map_err(|err| format!("failed to read {}: {err}", args.tasks.display()))?;
    let tasks = parse_csv(&csv)?;
    let witness = match thread_mode {
        ThreadMode::Serial => generate_witness(&tasks, &thread_mode)?,
        ThreadMode::Auto => generate_witness(&tasks, &thread_mode)?,
        ThreadMode::Fixed(n) => ThreadPoolBuilder::new()
            .num_threads(n)
            .build()
            .map_err(|err| format!("failed to build rayon thread pool: {err}"))?
            .install(|| generate_witness(&tasks, &thread_mode))?,
    };
    let json = serde_json::to_string_pretty(&witness)
        .map_err(|err| format!("failed to serialize witness: {err}"))?;
    fs::write(&args.out, format!("{json}\n"))
        .map_err(|err| format!("failed to write {}: {err}", args.out.display()))?;
    if let Some(path) = args.metrics_out {
        write_metrics(&path, &witness, &args.threads)?;
    }
    Ok(())
}

fn run_jittered_periodic_edf(args: JitteredPeriodicEdfArgs) -> Result<(), String> {
    let thread_mode = ThreadMode::parse(&args.threads)?;
    let csv = fs::read_to_string(&args.tasks)
        .map_err(|err| format!("failed to read {}: {err}", args.tasks.display()))?;
    let tasks = parse_jittered_csv(&csv)?;
    let witness = match thread_mode {
        ThreadMode::Serial => generate_jittered_witness(&tasks, &thread_mode)?,
        ThreadMode::Auto => generate_jittered_witness(&tasks, &thread_mode)?,
        ThreadMode::Fixed(n) => ThreadPoolBuilder::new()
            .num_threads(n)
            .build()
            .map_err(|err| format!("failed to build rayon thread pool: {err}"))?
            .install(|| generate_jittered_witness(&tasks, &thread_mode))?,
    };
    let json = serde_json::to_string_pretty(&witness)
        .map_err(|err| format!("failed to serialize witness: {err}"))?;
    fs::write(&args.out, format!("{json}\n"))
        .map_err(|err| format!("failed to write {}: {err}", args.out.display()))
}

fn write_metrics(path: &PathBuf, witness: &Witness, requested_threads: &str) -> Result<(), String> {
    let stats = &witness.generator_stats;
    let metrics = format!(
        concat!(
            "task_count,prefix_horizon,prefix_job_count,transport_basis_job_count,",
            "dbf_window_count,window_target_count,post_reset_window_target_count,",
            "requested_threads,status\n",
            "{},{},{},{},{},{},{},{},ok\n"
        ),
        stats.task_count,
        stats.prefix_horizon,
        stats.prefix_job_count,
        stats.transport_basis_job_count,
        witness.cert.dbf.ok_table.len(),
        stats.window_target_count,
        stats.post_reset_window_target_count,
        requested_threads
    );
    fs::write(path, metrics).map_err(|err| format!("failed to write {}: {err}", path.display()))
}

#[derive(Clone, Debug)]
enum ThreadMode {
    Serial,
    Fixed(usize),
    Auto,
}

impl ThreadMode {
    fn parse(text: &str) -> Result<Self, String> {
        match text {
            "auto" => Ok(Self::Auto),
            "1" => Ok(Self::Serial),
            _ => {
                let n = text
                    .parse::<usize>()
                    .map_err(|_| format!("invalid --threads value: {text}"))?;
                if n == 0 {
                    Err("--threads must be positive or auto".to_string())
                } else {
                    Ok(Self::Fixed(n))
                }
            }
        }
    }

    fn is_serial(&self) -> bool {
        matches!(self, Self::Serial)
    }
}

fn generate_witness(tasks: &[Task], thread_mode: &ThreadMode) -> Result<Witness, String> {
    let hyperperiod = tasks
        .iter()
        .try_fold(1, |acc, task| checked_lcm(acc, task.period))?;
    let max_offset = tasks.iter().map(|task| task.offset).max().unwrap_or(0);
    let max_deadline = tasks.iter().map(|task| task.deadline).max().unwrap_or(0);
    let base_horizon = max_offset
        .checked_add(checked_mul(2, hyperperiod)?)
        .and_then(|x| x.checked_add(max_deadline))
        .ok_or_else(|| "prefix horizon overflow".to_string())?;
    let residue_horizon = transport_residue_horizon(tasks, hyperperiod)?;
    let horizon = base_horizon.max(residue_horizon);
    ensure_limit(horizon <= MAX_HORIZON, "prefix horizon")?;

    let prefix_jobs = jobs_before(tasks, horizon)?;
    ensure_limit(prefix_jobs.len() <= MAX_BASIS_JOBS, "prefix job count")?;
    let slots = simulate_edf(&prefix_jobs, horizon);
    let completed_by = map_vec(thread_mode, &prefix_jobs, |job| {
        Ok(completion_time(&slots, job))
    })?;
    let backlog_free_matrix = backlog_matrix(thread_mode, &prefix_jobs, &completed_by)?;
    let prefix_basis_jobs = prefix_jobs.iter().map(|job| job.id).collect::<Vec<_>>();

    let transport_basis_jobs = transport_residue_jobs(tasks, hyperperiod)?;
    ensure_limit(
        transport_basis_jobs.len() <= MAX_BASIS_JOBS,
        "transport basis job count",
    )?;
    let transport_basis_job_count = transport_basis_jobs.len();
    let classes = map_vec(thread_mode, &transport_basis_jobs, |job_id| {
        Ok(TransportClass {
            rep_job: *job_id,
            completion_offset: hyperperiod,
            backlog_offset: hyperperiod,
        })
    })?;
    let job_class = (0..transport_basis_jobs.len())
        .map(|i| i as u64)
        .collect::<Vec<_>>();
    let job_shift = vec![hyperperiod; transport_basis_jobs.len()];

    let class_relevant_jobs = map_vec(thread_mode, &transport_basis_jobs, |job_id| {
        relevant_earlier_jobs(tasks, *job_id)
    })?;
    let window_target_certs =
        map_indexed_vec(thread_mode, &transport_basis_jobs, |class_id, target| {
            window_target_cert(tasks, hyperperiod, &transport_basis_jobs, class_id, *target)
        })?;

    let post_reset_horizon = checked_mul(2, hyperperiod)?
        .checked_add(max_deadline)
        .ok_or_else(|| "post-reset horizon overflow".to_string())?;
    ensure_limit(post_reset_horizon <= MAX_HORIZON, "post-reset horizon")?;
    let post_reset_jobs = jobs_before(tasks, post_reset_horizon)?;
    let mut post_reset_targets = post_reset_jobs.iter().map(|job| job.id).collect::<Vec<_>>();
    for job_id in &transport_basis_jobs {
        if !post_reset_targets.contains(job_id) {
            post_reset_targets.push(*job_id);
        }
    }
    post_reset_targets.sort_unstable();
    let post_reset_window_target_certs = map_vec(thread_mode, &post_reset_targets, |job_id| {
        let class_id = transport_class_for(tasks, hyperperiod, &transport_basis_jobs, *job_id)?;
        window_target_cert(tasks, hyperperiod, &transport_basis_jobs, class_id, *job_id)
    })?;

    let dbf_cutoff = scalar_dbf_cutoff(tasks, hyperperiod)?;
    ensure_limit(dbf_cutoff <= MAX_HORIZON, "DBF cutoff")?;
    let critical_points = critical_dbf_points(tasks, dbf_cutoff);
    let ok_table = map_vec(thread_mode, &critical_points, |t| {
        Ok(periodic_dbf(tasks, *t) <= *t)
    })?;

    Ok(Witness {
        schema_version: 1,
        policy: "periodic-edf",
        domain: "uniprocessor",
        task_hash: task_hash(tasks),
        generator: GeneratorInfo {
            name: "sched-witness-gen",
            version: "0.1",
        },
        cert: Cert {
            prefix: PrefixCert {
                horizon,
                basis_jobs: prefix_basis_jobs,
                slots,
                completed_by,
                backlog_free_matrix,
            },
            transport: TransportCert {
                period: hyperperiod,
                basis_jobs: transport_basis_jobs,
                classes,
                job_class,
                job_shift,
            },
            dbf: DbfCert {
                cutoff: dbf_cutoff,
                ok_table,
            },
        },
        sidecar: Sidecar {
            candidate_jobs: post_reset_jobs.iter().map(|job| job.id).collect(),
            class_relevant_jobs,
            window_target_certs,
            post_reset_window_target_certs,
        },
        generator_stats: GeneratorStats {
            task_count: tasks.len(),
            prefix_horizon: horizon,
            prefix_job_count: prefix_jobs.len(),
            transport_basis_job_count,
            window_target_count: transport_basis_job_count,
            post_reset_window_target_count: post_reset_jobs.len(),
            thread_mode: "deterministic".to_string(),
        },
    })
}

fn generate_jittered_witness(
    tasks: &[JitteredTask],
    thread_mode: &ThreadMode,
) -> Result<JitteredWitness, String> {
    let cutoff = jittered_dbf_cutoff(tasks)?;
    ensure_limit(cutoff <= MAX_HORIZON, "jittered DBF cutoff")?;
    let windows = jittered_critical_windows(tasks, cutoff)?;
    ensure_limit(
        windows.len() <= MAX_JITTERED_DBF_WINDOWS,
        "jittered DBF window count",
    )?;
    let ok_table = map_vec(thread_mode, &windows, |window| {
        Ok(jittered_window_demand(tasks, window[0], window[1])? <= window[1] - window[0])
    })?;
    if !ok_table.iter().all(|ok| *ok) {
        return Err("jittered DBF witness generation rejected unschedulable taskset".to_string());
    }
    Ok(JitteredWitness {
        schema_version: 2,
        policy: "jittered-periodic-edf",
        domain: "uniprocessor",
        task_hash: jittered_task_hash(tasks),
        generator: GeneratorInfo {
            name: "sched-witness-gen",
            version: "0.1",
        },
        cert: JitteredCert {
            dbf: JitteredDbfCert {
                cutoff,
                checked_windows: windows,
                all_windows_checked: true,
            },
        },
        generator_stats: JitteredGeneratorStats {
            task_count: tasks.len(),
            cutoff,
            checked_window_count: ok_table.len(),
            thread_mode: "deterministic".to_string(),
        },
    })
}

fn map_vec<T, U, F>(thread_mode: &ThreadMode, input: &[T], f: F) -> Result<Vec<U>, String>
where
    T: Sync,
    U: Send,
    F: Fn(&T) -> Result<U, String> + Sync + Send,
{
    if thread_mode.is_serial() {
        input.iter().map(f).collect()
    } else {
        input.par_iter().map(f).collect()
    }
}

fn map_indexed_vec<T, U, F>(thread_mode: &ThreadMode, input: &[T], f: F) -> Result<Vec<U>, String>
where
    T: Sync,
    U: Send,
    F: Fn(usize, &T) -> Result<U, String> + Sync + Send,
{
    if thread_mode.is_serial() {
        input
            .iter()
            .enumerate()
            .map(|(i, value)| f(i, value))
            .collect()
    } else {
        input
            .par_iter()
            .enumerate()
            .map(|(i, value)| f(i, value))
            .collect()
    }
}

fn parse_csv(content: &str) -> Result<Vec<Task>, String> {
    let rows = content
        .lines()
        .enumerate()
        .filter_map(|(index, line)| {
            let trimmed = line.trim();
            (!trimmed.is_empty() && !trimmed.starts_with('#')).then_some((index + 1, trimmed))
        })
        .collect::<Vec<_>>();
    if rows.is_empty() {
        return Err("empty CSV: expected at least one task row".to_string());
    }
    let rows = if is_header(rows[0].1) {
        &rows[1..]
    } else {
        &rows[..]
    };
    if rows.is_empty() {
        return Err("CSV contains a header but no task rows".to_string());
    }
    rows.iter().map(|row| parse_task_row(*row)).collect()
}

fn parse_jittered_csv(content: &str) -> Result<Vec<JitteredTask>, String> {
    let rows = content
        .lines()
        .enumerate()
        .filter_map(|(index, line)| {
            let trimmed = line.trim();
            (!trimmed.is_empty() && !trimmed.starts_with('#')).then_some((index + 1, trimmed))
        })
        .collect::<Vec<_>>();
    if rows.is_empty() {
        return Err("empty CSV: expected at least one task row".to_string());
    }
    let rows = if is_jittered_header(rows[0].1) {
        &rows[1..]
    } else {
        &rows[..]
    };
    if rows.is_empty() {
        return Err("CSV contains a header but no task rows".to_string());
    }
    rows.iter()
        .map(|row| parse_jittered_task_row(*row))
        .collect()
}

fn is_header(line: &str) -> bool {
    let cells = split_csv_line(line)
        .into_iter()
        .map(|cell| normalize_header_cell(&cell))
        .collect::<Vec<_>>();
    cells == ["cost", "period", "deadline"] || cells == ["cost", "period", "deadline", "offset"]
}

fn is_jittered_header(line: &str) -> bool {
    let cells = split_csv_line(line)
        .into_iter()
        .map(|cell| normalize_header_cell(&cell))
        .collect::<Vec<_>>();
    cells == ["cost", "period", "deadline", "offset", "jitter"]
        || cells == ["cost", "period", "deadline", "offset", "release_jitter"]
}

fn normalize_header_cell(cell: &str) -> String {
    cell.trim()
        .chars()
        .map(|c| {
            if c.is_whitespace() || c == '-' {
                '_'
            } else {
                c.to_ascii_lowercase()
            }
        })
        .collect()
}

fn parse_task_row((line_no, line): (usize, &str)) -> Result<Task, String> {
    let cells = split_csv_line(line);
    match cells.as_slice() {
        [cost, period, deadline] => Ok(Task {
            cost: parse_positive(line_no, "cost", cost)?,
            period: parse_positive(line_no, "period", period)?,
            deadline: parse_positive(line_no, "deadline", deadline)?,
            offset: 0,
        }),
        [cost, period, deadline, offset] => Ok(Task {
            cost: parse_positive(line_no, "cost", cost)?,
            period: parse_positive(line_no, "period", period)?,
            deadline: parse_positive(line_no, "deadline", deadline)?,
            offset: parse_nonnegative(line_no, "offset", offset)?,
        }),
        cols => Err(format!(
            "line {line_no}: expected 3 or 4 columns, got {}",
            cols.len()
        )),
    }
}

fn parse_jittered_task_row((line_no, line): (usize, &str)) -> Result<JitteredTask, String> {
    let cells = split_csv_line(line);
    match cells.as_slice() {
        [cost, period, deadline, offset, jitter] => Ok(JitteredTask {
            cost: parse_positive(line_no, "cost", cost)?,
            period: parse_positive(line_no, "period", period)?,
            deadline: parse_positive(line_no, "deadline", deadline)?,
            offset: parse_nonnegative(line_no, "offset", offset)?,
            jitter: parse_nonnegative(line_no, "jitter", jitter)?,
        }),
        cols => Err(format!(
            "line {line_no}: expected 5 columns, got {}",
            cols.len()
        )),
    }
}

fn split_csv_line(line: &str) -> Vec<String> {
    line.split(',')
        .map(|cell| cell.trim().to_string())
        .collect()
}

fn parse_positive(line_no: usize, name: &str, text: &str) -> Result<u64, String> {
    let value = text
        .parse::<u64>()
        .map_err(|_| format!("line {line_no}: invalid {name}: {text}"))?;
    if value == 0 {
        Err(format!("line {line_no}: {name} must be positive"))
    } else {
        Ok(value)
    }
}

fn parse_nonnegative(line_no: usize, name: &str, text: &str) -> Result<u64, String> {
    text.parse::<u64>()
        .map_err(|_| format!("line {line_no}: invalid {name}: {text}"))
}

fn jobs_before(tasks: &[Task], horizon: u64) -> Result<Vec<Job>, String> {
    let mut jobs = Vec::new();
    for (task_index, task) in tasks.iter().enumerate() {
        let mut index = 0;
        loop {
            let release = task
                .offset
                .checked_add(checked_mul(index, task.period)?)
                .ok_or_else(|| "job release overflow".to_string())?;
            if release >= horizon {
                break;
            }
            jobs.push(job_for(tasks, task_index, index)?);
            index += 1;
        }
    }
    Ok(jobs)
}

fn job_for(tasks: &[Task], task_index: usize, index: u64) -> Result<Job, String> {
    let task = &tasks[task_index];
    let release = task
        .offset
        .checked_add(checked_mul(index, task.period)?)
        .ok_or_else(|| "job release overflow".to_string())?;
    let deadline = release
        .checked_add(task.deadline)
        .ok_or_else(|| "job deadline overflow".to_string())?;
    Ok(Job {
        id: task_index as u64 + tasks.len() as u64 * index,
        task: task_index,
        index,
        release,
        cost: task.cost,
        deadline,
    })
}

fn job_by_id(tasks: &[Task], job_id: u64) -> Result<Job, String> {
    if tasks.is_empty() {
        return Err("empty taskset".to_string());
    }
    let task_index = (job_id % tasks.len() as u64) as usize;
    let index = job_id / tasks.len() as u64;
    job_for(tasks, task_index, index)
}

fn simulate_edf(jobs: &[Job], horizon: u64) -> Vec<Option<u64>> {
    let mut remaining = jobs
        .iter()
        .map(|job| (job.id, job.cost))
        .collect::<Vec<_>>();
    let mut slots = Vec::with_capacity(horizon as usize);
    for t in 0..horizon {
        let selected = jobs
            .iter()
            .filter(|job| job.release <= t && remaining_of(&remaining, job.id) > 0)
            .min_by(|a, b| match a.deadline.cmp(&b.deadline) {
                Ordering::Equal => a.id.cmp(&b.id),
                other => other,
            })
            .map(|job| job.id);
        if let Some(job_id) = selected {
            if let Some((_, left)) = remaining.iter_mut().find(|(id, _)| *id == job_id) {
                *left = left.saturating_sub(1);
            }
        }
        slots.push(selected);
    }
    slots
}

fn remaining_of(remaining: &[(u64, u64)], job_id: u64) -> u64 {
    remaining
        .iter()
        .find(|(id, _)| *id == job_id)
        .map(|(_, left)| *left)
        .unwrap_or(0)
}

fn completion_time(slots: &[Option<u64>], job: &Job) -> u64 {
    let mut service = 0;
    for (t, slot) in slots.iter().enumerate() {
        if *slot == Some(job.id) {
            service += 1;
        }
        if service >= job.cost {
            return (t + 1) as u64;
        }
    }
    slots.len() as u64
}

fn backlog_matrix(
    thread_mode: &ThreadMode,
    jobs: &[Job],
    completed_by: &[u64],
) -> Result<Vec<Vec<bool>>, String> {
    map_vec(thread_mode, jobs, |target| {
        Ok(completed_by
            .iter()
            .map(|completion| *completion <= target.release)
            .collect())
    })
}

fn transport_residue_jobs(tasks: &[Task], period: u64) -> Result<Vec<u64>, String> {
    let mut jobs = Vec::new();
    for task_index in 0..tasks.len() {
        for index in 0..period {
            jobs.push(job_for(tasks, task_index, index)?.id);
        }
    }
    Ok(jobs)
}

fn transport_residue_horizon(tasks: &[Task], hyperperiod: u64) -> Result<u64, String> {
    let mut horizon = 0;
    for task_index in 0..tasks.len() {
        for index in 0..hyperperiod {
            let job = job_for(tasks, task_index, index)?;
            horizon = horizon.max(
                job.deadline
                    .checked_add(1)
                    .ok_or_else(|| "transport residue horizon overflow".to_string())?,
            );
        }
    }
    Ok(horizon)
}

fn relevant_earlier_jobs(tasks: &[Task], target_id: u64) -> Result<Vec<u64>, String> {
    let target = job_by_id(tasks, target_id)?;
    let horizon = target
        .deadline
        .checked_add(1)
        .ok_or_else(|| "window target horizon overflow".to_string())?;
    Ok(jobs_before(tasks, horizon)?
        .into_iter()
        .filter(|job| job.release < target.release && job.deadline <= target.deadline)
        .map(|job| job.id)
        .collect())
}

fn window_target_cert(
    tasks: &[Task],
    hyperperiod: u64,
    transport_basis: &[u64],
    class_id: usize,
    target_id: u64,
) -> Result<WindowTargetCert, String> {
    let rep_id = transport_basis[class_id];
    let target = job_by_id(tasks, target_id)?;
    let rep = job_by_id(tasks, rep_id)?;
    if target.release < rep.release {
        return Err("target release precedes representative release".to_string());
    }
    let delta = target.release - rep.release;
    let rep_relevant = relevant_earlier_jobs(tasks, rep_id)?;
    let pairs = relevant_earlier_jobs(tasks, target_id)?
        .into_iter()
        .map(|earlier_id| {
            let earlier = job_by_id(tasks, earlier_id)?;
            let rep_earlier = rep_relevant
                .iter()
                .copied()
                .find(|candidate_id| {
                    job_by_id(tasks, *candidate_id)
                        .map(|candidate| {
                            candidate.release.checked_add(delta) == Some(earlier.release)
                                && candidate.deadline.checked_add(delta) == Some(earlier.deadline)
                                && candidate.cost == earlier.cost
                        })
                        .unwrap_or(false)
                })
                .ok_or_else(|| {
                    format!("missing representative earlier job for target job {earlier_id}")
                })?;
            Ok(WindowPairCert {
                target_earlier_job: earlier_id,
                rep_earlier_job: rep_earlier,
                delta,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(WindowTargetCert {
        target_job: target_id,
        class_id: class_id as u64,
        shift: hyperperiod,
        pairs,
    })
}

fn transport_class_for(
    tasks: &[Task],
    hyperperiod: u64,
    basis: &[u64],
    job_id: u64,
) -> Result<usize, String> {
    if let Some(position) = basis.iter().position(|basis_id| *basis_id == job_id) {
        return Ok(position);
    }
    let target = job_by_id(tasks, job_id)?;
    let residue_span = hyperperiod / tasks[target.task].period;
    basis
        .iter()
        .position(|basis_id| {
            job_by_id(tasks, *basis_id)
                .map(|basis_job| {
                    basis_job.task == target.task && basis_job.index == target.index % residue_span
                })
                .unwrap_or(false)
        })
        .ok_or_else(|| format!("missing transport class for job {job_id}"))
}

fn scalar_dbf_cutoff(tasks: &[Task], hyperperiod: u64) -> Result<u64, String> {
    let sum_deadlines = tasks
        .iter()
        .try_fold(0_u64, |acc, task| acc.checked_add(task.deadline).ok_or(()))
        .map_err(|_| "DBF cutoff overflow".to_string())?;
    sum_deadlines
        .checked_add(hyperperiod)
        .ok_or_else(|| "DBF cutoff overflow".to_string())
}

fn critical_dbf_points(tasks: &[Task], cutoff: u64) -> Vec<u64> {
    let mut points = (0..=cutoff).collect::<Vec<_>>();
    for task_index in 0..tasks.len() {
        let mut index = 0;
        loop {
            let Ok(job) = job_for(tasks, task_index, index) else {
                break;
            };
            if job.deadline > cutoff {
                break;
            }
            points.push(job.deadline);
            index += 1;
        }
    }
    points
}

fn periodic_dbf(tasks: &[Task], h: u64) -> u64 {
    tasks
        .iter()
        .map(|task| {
            if h < task.deadline {
                0
            } else {
                (1 + (h - task.deadline) / task.period) * task.cost
            }
        })
        .sum()
}

fn jittered_dbf_cutoff(tasks: &[JitteredTask]) -> Result<u64, String> {
    let hyperperiod = tasks
        .iter()
        .try_fold(1, |acc, task| checked_lcm(acc, task.period))?;
    let max_offset = tasks.iter().map(|task| task.offset).max().unwrap_or(0);
    let max_deadline = tasks.iter().map(|task| task.deadline).max().unwrap_or(0);
    let max_jitter = tasks.iter().map(|task| task.jitter).max().unwrap_or(0);
    let horizon_base = max_offset
        .checked_add(max_deadline)
        .and_then(|x| x.checked_add(hyperperiod))
        .ok_or_else(|| "jittered DBF cutoff overflow".to_string())?;
    let offset_cutoff = horizon_base
        .checked_add(checked_mul(
            horizon_base
                .checked_add(1)
                .ok_or_else(|| "jittered DBF cutoff overflow".to_string())?,
            hyperperiod,
        )?)
        .ok_or_else(|| "jittered DBF cutoff overflow".to_string())?;
    offset_cutoff
        .checked_add(max_jitter)
        .ok_or_else(|| "jittered DBF cutoff overflow".to_string())
}

fn jittered_critical_points(tasks: &[JitteredTask], cutoff: u64) -> Result<Vec<u64>, String> {
    let mut points = (0..=cutoff).collect::<Vec<_>>();
    for task in tasks {
        for index in 0..=cutoff {
            let release = task
                .offset
                .checked_add(checked_mul(index, task.period)?)
                .ok_or_else(|| "jittered deadline point overflow".to_string())?;
            let deadline = release
                .checked_add(task.deadline)
                .ok_or_else(|| "jittered deadline point overflow".to_string())?;
            if deadline <= cutoff {
                points.push(deadline);
            } else {
                break;
            }
        }
    }
    Ok(points)
}

fn jittered_critical_windows(tasks: &[JitteredTask], cutoff: u64) -> Result<Vec<[u64; 2]>, String> {
    let points = jittered_critical_points(tasks, cutoff)?;
    let mut windows = Vec::new();
    for t1 in &points {
        for t2 in &points {
            if t1 <= t2 && *t2 <= cutoff {
                windows.push([*t1, *t2]);
            }
        }
    }
    Ok(windows)
}

fn jittered_window_demand(tasks: &[JitteredTask], t1: u64, t2: u64) -> Result<u64, String> {
    tasks.iter().try_fold(0_u64, |acc, task| {
        let count = jittered_task_window_count(task, t1, t2)?;
        let demand = checked_mul(count, task.cost)?;
        acc.checked_add(demand)
            .ok_or_else(|| "jittered DBF demand overflow".to_string())
    })
}

fn jittered_task_window_count(task: &JitteredTask, t1: u64, t2: u64) -> Result<u64, String> {
    let mut count = 0_u64;
    for index in 0..=t2 {
        if task.deadline <= t2 {
            let release = task
                .offset
                .checked_add(checked_mul(index, task.period)?)
                .ok_or_else(|| "jittered release overflow".to_string())?;
            let latest = release
                .checked_add(task.jitter)
                .ok_or_else(|| "jittered latest release overflow".to_string())?;
            let deadline_release_latest = t2 - task.deadline;
            if t1.max(release) <= deadline_release_latest.min(latest) {
                count = count
                    .checked_add(1)
                    .ok_or_else(|| "jittered DBF count overflow".to_string())?;
            }
        }
    }
    Ok(count)
}

fn task_hash(tasks: &[Task]) -> String {
    let mut canonical = String::from("schema=periodic-edf-tasks-v1\ncost,period,deadline,offset\n");
    for task in tasks {
        canonical.push_str(&format!(
            "{},{},{},{}\n",
            task.cost, task.period, task.deadline, task.offset
        ));
    }
    let digest = Sha256::digest(canonical.as_bytes());
    format!("sha256:{digest:x}")
}

fn jittered_task_hash(tasks: &[JitteredTask]) -> String {
    let digest = Sha256::digest(canonical_jittered_task_text(tasks).as_bytes());
    format!("sha256:{digest:x}")
}

fn canonical_jittered_task_text(tasks: &[JitteredTask]) -> String {
    let mut canonical =
        String::from("schema=jittered-periodic-edf-tasks-v2\ncost,period,deadline,offset,jitter\n");
    for task in tasks {
        canonical.push_str(&format!(
            "{},{},{},{},{}\n",
            task.cost, task.period, task.deadline, task.offset, task.jitter
        ));
    }
    canonical
}

fn checked_gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn checked_lcm(a: u64, b: u64) -> Result<u64, String> {
    checked_mul(a / checked_gcd(a, b), b)
}

fn checked_mul(a: u64, b: u64) -> Result<u64, String> {
    a.checked_mul(b)
        .ok_or_else(|| "integer overflow".to_string())
}

fn ensure_limit(ok: bool, what: &str) -> Result<(), String> {
    if ok {
        Ok(())
    } else {
        Err(format!("{what} exceeds PR2 resource limit"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_jittered_csv_with_jitter_header() {
        let tasks = parse_jittered_csv("cost,period,deadline,offset,jitter\n1,4,4,0,1\n")
            .expect("jittered CSV should parse");
        assert_eq!(
            tasks,
            vec![JitteredTask {
                cost: 1,
                period: 4,
                deadline: 4,
                offset: 0,
                jitter: 1,
            }]
        );
    }

    #[test]
    fn parses_jittered_csv_with_release_jitter_header() {
        let tasks = parse_jittered_csv("cost,period,deadline,offset,release_jitter\n2,5,5,3,2\n")
            .expect("release_jitter CSV should parse");
        assert_eq!(
            tasks,
            vec![JitteredTask {
                cost: 2,
                period: 5,
                deadline: 5,
                offset: 3,
                jitter: 2,
            }]
        );
    }

    #[test]
    fn rejects_non_jittered_csv_shapes() {
        let err = parse_jittered_csv("cost,period,deadline,offset\n1,4,4,0\n")
            .expect_err("four-column CSV must be rejected");
        assert!(err.contains("expected 5 columns"));
    }

    #[test]
    fn rejects_invalid_jittered_values() {
        let err = parse_jittered_csv("cost,period,deadline,offset,jitter\n0,4,4,0,1\n")
            .expect_err("zero cost must be rejected");
        assert!(err.contains("cost must be positive"));

        let err = parse_jittered_csv("cost,period,deadline,offset,jitter\n1,4,4,0,-1\n")
            .expect_err("negative jitter must be rejected");
        assert!(err.contains("invalid jitter"));
    }

    #[test]
    fn hashes_canonical_jittered_task_text() {
        let tasks = parse_jittered_csv("cost,period,deadline,offset,jitter\n1,1,1,0,0\n")
            .expect("jittered CSV should parse");
        assert_eq!(
            canonical_jittered_task_text(&tasks),
            "schema=jittered-periodic-edf-tasks-v2\ncost,period,deadline,offset,jitter\n1,1,1,0,0\n"
        );
        assert_eq!(
            jittered_task_hash(&tasks),
            "sha256:4d975dd17f1887dc34f2607b632fe1430a674efa7c5c6ad07b8116697b490011"
        );

        let tasks =
            parse_jittered_csv("cost,period,deadline,offset,jitter\n1,4,4,0,1\n2,5,5,3,2\n")
                .expect("multi-row jittered CSV should parse");
        assert_eq!(
            jittered_task_hash(&tasks),
            "sha256:fea75940a9369d5153b5bd0e6c0e11ca396332982ad218873590323f77a74b73"
        );
    }

    #[test]
    fn computes_tiny_jittered_cutoff() {
        let tasks = parse_jittered_csv("cost,period,deadline,offset,jitter\n1,1,1,0,0\n")
            .expect("tiny jittered CSV should parse");
        assert_eq!(jittered_dbf_cutoff(&tasks).unwrap(), 5);
    }

    #[test]
    fn preserves_tiny_critical_window_order() {
        let tasks = parse_jittered_csv("cost,period,deadline,offset,jitter\n1,1,1,0,0\n")
            .expect("tiny jittered CSV should parse");
        let windows = jittered_critical_windows(&tasks, 1).unwrap();
        assert_eq!(
            windows,
            vec![[0, 0], [0, 1], [0, 1], [1, 1], [1, 1], [1, 1], [1, 1]]
        );
    }

    #[test]
    fn generates_tiny_jittered_witness() {
        let tasks = parse_jittered_csv("cost,period,deadline,offset,jitter\n1,1,1,0,0\n")
            .expect("tiny jittered CSV should parse");
        let witness = generate_jittered_witness(&tasks, &ThreadMode::Serial).unwrap();
        assert_eq!(witness.schema_version, 2);
        assert_eq!(witness.policy, "jittered-periodic-edf");
        assert_eq!(witness.cert.dbf.cutoff, 5);
        assert!(witness.cert.dbf.all_windows_checked);
        assert_eq!(
            witness.task_hash,
            "sha256:4d975dd17f1887dc34f2607b632fe1430a674efa7c5c6ad07b8116697b490011"
        );
    }

    #[test]
    fn rejects_unschedulable_jittered_taskset() {
        let tasks = parse_jittered_csv("cost,period,deadline,offset,jitter\n2,1,1,0,0\n")
            .expect("unschedulable jittered CSV should parse");
        let err = generate_jittered_witness(&tasks, &ThreadMode::Serial)
            .expect_err("unschedulable taskset should not generate a witness");
        assert!(err.contains("rejected unschedulable taskset"));
    }
}
