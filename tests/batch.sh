#!/bin/bash
#该脚本在目录下为每个Cargo项目执行相同的命令直到报错

# All arguments passed to this script are forwarded to cargo rapx
# Example: batch.sh -F -M

cur=$(pwd)

# 查找并编译当前目录下的所有 Rust 项目
find support -type f -name "Cargo.toml" | while read -r cargo_file; do
  # 获取 Cargo.toml 文件所在的目录
  project_dir=$(dirname "$cargo_file")

  echo "Processing project in: $project_dir"

  # 切换到项目目录
  pushd "$project_dir" >/dev/null

  if [ $# -eq 0 ]; then
    #脚本无参数时执行cargo clean
    #Example: batch.sh
    cmd="cargo clean"
    $cmd
    # 返回原始目录
    popd >/dev/null
    continue
  else
    cmd="cargo rapx $@"
    $cmd 2>&1 | tee $cur/rapx.txt | ansi2txt | grep 'RAP|WARN|' && echo -e "\033[32m$project_dir pass\033[0m"
  fi

  if [ $? -ne 0 ]; then
    echo -e "\033[31mError: '$cmd' doesn't emit WARN diagnostics in $project_dir \033[0m\nRAP output:"
    cat $cur/rapx.txt
    exit 1
  fi

  cat $cur/rapx.txt | ansi2txt | grep 'RAP|ERROR|'
  if [ $? -eq 0 ]; then
    echo -e "Error: '$cmd' contains error message in $project_dir \nRAP output:"
    cat $cur/rapx.txt
    exit 1
  fi

  # 返回原始目录
  popd >/dev/null
done
